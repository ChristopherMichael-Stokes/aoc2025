# /// script
# requires-python = ">=3.14"
# dependencies = [
#     "numpy",
# ]
# ///
import re
import numpy as np
import numpy.typing as npt

BLOCK_MAP: dict[str, int] = {"#": 1, ".": 0}

def parse_inputs(inputs: list[str]) -> tuple[list[list[npt.NDArray]], list[npt.NDArray], list[list[int]]]:
    blocks_: list[list[int]] = [] 
    grids: list[npt.NDArray] = [] 
    grids_requirements: list[list[int]] = []

    for line in inputs:
        if re.match(r"^\d+x\d+:[ \d]+$", line):  # Grid spec
            # Parse grid + skip to next iteration
            xy, reqs = line.split(': ')
            x, y = [int(a) for a in xy.split('x')]
            grids.append(np.zeros((y, x), dtype=np.int8))

            requirements = [int(a) for a in reqs.split()]
            requirements = [idx for (idx, r) in enumerate(requirements) for _ in range(r)]
            grids_requirements.append(requirements)
            continue # Make sure we don't try parsing a block

        elif re.match(r"^\d+:$", line):  # Block idx
            blocks_.append([])
            continue

        # Parse block, adding row to curernt block idx
        blocks_[-1].append([BLOCK_MAP[c] for c in line])  # type: ignore[invalid-argument-type]

    #  Get all unique rotations + flips of each block
    blocks = []
    for b in blocks_:
        block = np.array(b, dtype=np.int8)
        rotations = [block] + [np.rot90(block, i) for i in range(1,4)]
        flips = [np.flip(r, i) for r in rotations for i in range(2)]
        block_variants = []
        for f in flips:
            if not any((f == bv).all() for bv in block_variants):
                block_variants.append(f)

        blocks.append(block_variants)

    if len(inputs) < 50: # Dummy inputs
        for b in blocks:
            print(b)
            print()

        for g, gr in zip(grids, grids_requirements):
            print(g)
            print(gr)
            print()

    return blocks, grids, grids_requirements


def part01(inputs: list[str]) -> None:
    blocks, grids, grids_requirements = parse_inputs(inputs)
    solveable = np.ones(len(grids))

    # Brute force will not be possibe imo, though could throw togethr
    # enough heuristics to check if inputs are incompatible rather
    # than look for possible solution?

    # If we get to a point where a solution may be possible then try the brue-force check?
    #  -> hopefully we can then get to a solution quick enough

    for idx, (grid, grid_requirements) in enumerate(zip(grids, grids_requirements)):
        grid_area = grid.shape[0] * grid.shape[1]
        block_units = sum(blocks[r][0].sum() for r in grid_requirements)

        print(grid_area, block_units)

        if grid_area < block_units:
            solveable[idx] = 0
            continue

    print(solveable)
    


def part02(inputs: list[str]) -> None:
    pass   


if __name__=="__main__":
    input_file = 'inputs.txt'
    input_file = 'sample.txt'
    with open(input_file, 'r') as f: 
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
