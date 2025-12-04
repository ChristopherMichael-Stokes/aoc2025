# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from typing import Sequence
from dataclasses import dataclass
from copy import deepcopy


OPEN = '.'
USED = 'x'
BLOCKED = '@'
THRESHOLD = 4


@dataclass
class Grid:
    grid: list[list[str]]
    n_rows: int
    n_cols: int


    @classmethod
    def make_padded(cls, inputs: list[str]) -> "Grid":
        grid = [list(f'{OPEN}{line}{OPEN}') for line in inputs]
        padding = list(OPEN * len(grid[0]))
        grid = [padding, *grid, padding]
        return cls(grid, len(grid), len(grid[0]))


    def get_adjacent(self, row_idx: int, col_idx: int) -> list[str]:
        adjacents = []
        for i in range(row_idx - 1, row_idx + 2):
            for j in range(col_idx - 1, col_idx + 2):
                if i == row_idx and j == col_idx:
                    continue
                adjacents.append(self.grid[i][j])

        return adjacents


    def __getitem__(self, pos: tuple[int, int]) -> str:
        return self.grid[pos[0]][pos[1]]


    def __setitem__(self, pos: tuple[int, int], val: str) -> None:
        self.grid[pos[0]][pos[1]] = val


    def __repr__(self):
        return '\n'.join(str(r) for r in self.grid)


def plot_accessible(grid: Grid, t: int) -> Grid:
    next_grid = deepcopy(grid)
    start, end = (1,1), (grid.n_rows - 2, grid.n_cols - 2)

    for i in range(start[0], end[0] + 1):
        for j in range(start[1], end[1] + 1):
            if grid[i, j] == BLOCKED:
                connected = [x for x in grid.get_adjacent(i,j) if x == BLOCKED]
                if len(connected) < t:
                    next_grid[i, j] = USED

    return next_grid


def part01(inputs: list[str]) -> None:
    n_rolls = 0
    grid = Grid.make_padded(inputs)
    accessible = plot_accessible(grid, THRESHOLD)
    n_rolls = sum([r.count(USED) for r in accessible.grid])

    # print(next_grid)
    print(f'{n_rolls=}')


def part02(inputs: list[str]) -> None:
    n_rolls_current, n_rolls_next = 0, -1
    grid = Grid.make_padded(inputs)

    while n_rolls_current != n_rolls_next:
        n_rolls_current = n_rolls_next
        grid = plot_accessible(grid, THRESHOLD)
        n_rolls_next = sum([r.count(USED) for r in grid.grid])

    # print(next_grid)
    print(f'{n_rolls_current=}')
    pass
    

if __name__=="__main__":
    input_file = 'sample.txt'
    input_file = 'inputs.txt'
    with open(input_file, 'r') as f: 
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)

