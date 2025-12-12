# /// script
# requires-python = ">=3.14"
# dependencies = [
#     "numpy",
#     "z3-solver",
# ]
# ///
import re
from typing import NamedTuple
import numpy as np
import numpy.typing as npt
from z3 import z3

z3.set_param("parallel.enable", True)
BLOCK_MAP: dict[str, int] = {"#": 1, ".": 0}


def parse_inputs(
    inputs: list[str],
) -> tuple[list[list[npt.NDArray]], list[npt.NDArray], list[list[int]]]:
    blocks_: list[list[int]] = []
    grids: list[npt.NDArray] = []
    grids_requirements: list[list[int]] = []

    for line in inputs:
        if re.match(r"^\d+x\d+:[ \d]+$", line):  # Grid spec
            # Parse grid + skip to next iteration
            xy, reqs = line.split(": ")
            x, y = [int(a) for a in xy.split("x")]
            grids.append(np.zeros((y, x), dtype=np.int8))

            requirements = [int(a) for a in reqs.split()]
            requirements = [
                idx for (idx, r) in enumerate(requirements) for _ in range(r)
            ]
            grids_requirements.append(requirements)
            continue  # Make sure we don't try parsing a block

        elif re.match(r"^\d+:$", line):  # Block idx
            blocks_.append([])
            continue

        # Parse block, adding row to curernt block idx
        blocks_[-1].append([BLOCK_MAP[c] for c in line])  # type: ignore[invalid-argument-type]

    #  Get all unique rotations + flips of each block
    blocks = []
    for b in blocks_:
        block = np.array(b, dtype=np.int8)
        rotations = [block] + [np.rot90(block, i) for i in range(1, 4)]
        flips = [np.flip(r, i) for r in rotations for i in range(2)]
        block_variants = []
        for f in flips:
            if not any((f == bv).all() for bv in block_variants):
                block_variants.append(f)

        blocks.append(block_variants)

    if len(inputs) < 50:  # Dummy inputs
        for b in blocks:
            print(b)
            print()

        for g, gr in zip(grids, grids_requirements):
            print(g)
            print(gr)
            print()

    return blocks, grids, grids_requirements


class BlockConstraints(NamedTuple):
    used: z3.BoolRef
    x: z3.ArithRef
    y: z3.ArithRef
    variant: npt.NDarray
    block_id: int


def can_solve_slow(
    blocks: list[list[npt.NDArray]], grid: npt.NDArray, grid_requirements: list[int]
) -> bool:
    # Integer programming type approach - works well for small inputs
    # but is intractible for unsolveable problems or problems with a lot of boxes
    # as we have an insane amount of constraints r.e. overlapping logic
    grid_height, grid_width = grid.shape
    grid_area: int = grid_height * grid_width
    block_units: int = sum(blocks[r][0].sum() for r in grid_requirements)

    if grid_area < block_units:
        return False

    available_blocks: list[list[npt.NDArray]] = [blocks[r] for r in grid_requirements]
    solver = z3.Solver()

    # For each block + variant, model it via a boolean is_used, + x & y of top left corner
    blocks_constraints: list[list[BlockConstraints]] = []
    for i, block_variants in enumerate(available_blocks):
        blocks_constraints.append([])
        for j, variant in enumerate(block_variants):
            block_id = f"block{i}_variant{j}"
            used = z3.Bool(f"{block_id}_used")
            x = z3.Int(f"{block_id}_x")
            y = z3.Int(f"{block_id}_y")
            # If a block is active, x & y must be within the grid
            block_height, block_width = variant.shape

            block_within_bounds = z3.And(
                x >= 0,
                x + block_width <= grid_width,
                y >= 0,
                y + block_height <= grid_height,
            )
            solver.add(z3.Implies(used, block_within_bounds))
            constraints = BlockConstraints(used=used, x=x, y=y, variant=variant, block_id=i*10+j)
            blocks_constraints[-1].append(constraints)

        # For each block, only one variant can be active
        actives = [bc.used for bc in blocks_constraints[-1]]
        solver.add(z3.Sum(actives) == 1)

    # For each block that is active, it must not overlap with any other active variants of other blocks
    for i in range(len(blocks_constraints)):
        # The block we want to add conditions for
        current_variants, other_variants = (
            blocks_constraints[i],
            blocks_constraints[i + 1 :],
        )
        if not other_variants:  # Hit end of list
            break

        for cv in current_variants:
            for ovs in other_variants:
                for ov in ovs:
                    both_active = z3.And(cv.used, ov.used)
                    # For each point in both blocks, no two active bits can share the same x,y?
                    # Get all occupied cell offsets for each variant
                    cv_cells = [
                        (dy, dx)
                        for dy in range(cv.variant.shape[0])
                        for dx in range(cv.variant.shape[1])
                        if cv.variant[dy, dx] == 1
                    ]

                    ov_cells = [
                        (dy, dx)
                        for dy in range(ov.variant.shape[0])
                        for dx in range(ov.variant.shape[1])
                        if ov.variant[dy, dx] == 1
                    ]

                    # Check if any pair of cells collide
                    cell_collisions = []
                    for dy1, dx1 in cv_cells:
                        for dy2, dx2 in ov_cells:
                            # These cells collide if they're at the same grid position
                            same_position = z3.And(
                                cv.x + dx1 == ov.x + dx2, cv.y + dy1 == ov.y + dy2
                            )
                            cell_collisions.append(same_position)

                    has_overlap = z3.Or(cell_collisions)
                    solver.add(z3.Implies(both_active, z3.Not(has_overlap)))

    solved = solver.check()
    if solved == z3.sat:
        model = solver.model()
        print(model)

    return solved == z3.sat


def can_solve_less_slow(
    blocks: list[list[npt.NDArray]], grid: npt.NDArray, grid_requirements: list[int]
) -> bool:
    # More z3, this time modelling the grid cells as containing the id
    # of each block variant placed in it (like demonstrated in the 
    # complete examples).  Is a little faster as there is less total constraints,
    # but still probably intractable for large problem spaces
    grid_height, grid_width = grid.shape
    grid_area: int = grid_height * grid_width
    block_units: int = sum(blocks[r][0].sum() for r in grid_requirements)

    if grid_area < block_units:
        return False

    available_blocks: list[list[npt.NDArray]] = [blocks[r] for r in grid_requirements]
    solver = z3.Solver()
    # Random chatgpt suggested optimisation params - does actually have >2x speedup though not sure how it effects scalability
    solver.set('random_seed', 42)  # Reproducibility
    solver.set('phase_selection', 0)  # Try different phase selection (0-5)
    solver.set('restart_strategy', 1)  # Geometric restarts
    solver.set('restart_factor', 1.5)  # More aggressive restarts
    solver.set('arith.solver', 2)  # Try different arithmetic solvers (1-6)
    solver.set('arith.propagate_eqs', True)  # Propagate equalities eagerly
    solver.set('arith.eager_eq_axioms', True)
    solver.set('solve_eqs', True)  # Solve equations to reduce variables
    solver.set('elim_unconstrained', True)  # Eliminate unconstrained vars
    solver.set('relevancy', 2)  # Maximum relevancy (0-2)

    z3_grid: list[list[z3.ArithRef]] = [
        [z3.Int(f"cell_{i}_{j}") for j in range(grid_width)] for i in range(grid_height)
    ]
    # Each cell must be between 0 or 1
    for row in z3_grid:
        for cell in row:
            # solver.add(z3.And(cell >= 0, cell <= 1))
            solver.add(cell >= 0)

    # For each block + variant, model it via a boolean is_used, + x & y of top left corner
    blocks_constraints: list[list[BlockConstraints]] = []
    for i, block_variants in enumerate(available_blocks):
        blocks_constraints.append([])
        for j, variant in enumerate(block_variants):
            block_id = f"block{i}_variant{j}"
            used = z3.Bool(f"{block_id}_used")
            x = z3.Int(f"{block_id}_x")
            y = z3.Int(f"{block_id}_y")
            # If a block is active, x & y must be within the grid
            block_height, block_width = variant.shape

            block_within_bounds = z3.And(
                x >= 0,
                x + block_width <= grid_width,
                y >= 0,
                y + block_height <= grid_height,
            )
            solver.add(z3.Implies(used, block_within_bounds))

            constraints = BlockConstraints(used=used, x=x, y=y, variant=variant, block_id=i*10+j)
            blocks_constraints[-1].append(constraints)

        # For each block, only one variant can be active
        actives = [bc.used for bc in blocks_constraints[-1]]
        solver.add(z3.Sum(actives) == 1)

    # For each block that is active, it must not overlap with any other active variants of other blocks
    for block_constraints in blocks_constraints:
        for bc in block_constraints:
            # For every possible cell in the grid,
            # if the block is used and on that cell,
            # the cell value will be the id of the block
            for y, row in enumerate(z3_grid):
                for x, cell in enumerate(row):
                    if y + bc.variant.shape[0] <= grid_height and x + bc.variant.shape[1] <= grid_width:
                        covered_cells = [
                            (dy, dx)
                            for dy in range(bc.variant.shape[0])
                            for dx in range(bc.variant.shape[1])
                            if bc.variant[dy, dx] == 1
                        ]
                        for (dy, dx) in covered_cells:
                            solver.add(z3.Implies(
                                z3.And(bc.used, bc.x == x, bc.y == y),
                                z3_grid[y+dy][x+dx] == bc.block_id,
                            ))

    solved = solver.check()
    if solved == z3.sat:
        model = solver.model()
        print(model)

    return solved == z3.sat


def part01(inputs: list[str]) -> None:
    blocks, grids, grids_requirements = parse_inputs(inputs)
    solvable = []
    for idx, (grid, grid_requirements) in enumerate(zip(grids, grids_requirements)):
        # solvable.append(can_solve_slow(blocks, grid, grid_requirements))
        solvable.append(can_solve_less_slow(blocks, grid, grid_requirements))

    print(solvable)
    print(f"{sum(solvable)=}")


def part02(inputs: list[str]) -> None:
    pass


if __name__ == "__main__":
    input_file = "inputs.txt"
    input_file = "sample.txt"
    with open(input_file, "r") as f:
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
