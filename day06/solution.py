# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from operator import add, mul
from functools import reduce
from itertools import pairwise
from typing import Callable
import re


OP_MAP: dict[str, Callable[[int, int], int]] = {'+': add, '*': mul}


def accumulate(columns: list[list[int]], operators: list[Callable[[int, int], int]]) -> int:
    return sum(reduce(op, col) for (col, op) in zip(columns, operators))


def part01(inputs: list[str]) -> None:
    n_rows, n_cols = len(inputs) - 1, len(inputs[0].split())
    columns = [[] for _ in range(n_cols)]

    for i in range(n_rows):
        for (j, value) in enumerate(inputs[i].split()):
            columns[j].append(int(value))

    operators = [OP_MAP[x] for x in inputs[n_rows].split()]
    total = accumulate(columns, operators)

    print(f"{total=}")


def part02(inputs: list[str]) -> None:
    # Find locations of operators on bottom row as start and end point
    # for each column
    idxs_operators = [(m.start(), OP_MAP[m.group()]) for m in re.finditer(r'[\+,\*]', inputs[-1])]
    idxs, operators = zip(*idxs_operators)
    idxs = [*idxs, len(inputs[0])]

    # Split inputs into columns preserving whitespace 
    columns = [[] for _ in range(len(operators))]
    n_rows = len(inputs) - 1
    
    for col_idx, (start, end) in enumerate(pairwise(idxs)):
        for i in range(n_rows):
            columns[col_idx].append(inputs[i][start:end-1])
    
    # Parse corrected column values left to right, top to bottom
    new_columns = [[] for _ in range(len(operators))]

    for c_old, c_new in zip(columns, new_columns):
        n_items, col_width = len(c_old), len(c_old[0])
        for j in range(col_width):
            col_value = 0
            for i in range(n_items):
                if c_old[i][j].isalnum():
                    col_value = (10 * col_value) + int(c_old[i][j])
            c_new.append(col_value)

    total = accumulate(new_columns, operators)
    print(f"{total=}")


if __name__=="__main__":
    input_file = 'sample.txt'
    input_file = 'inputs.txt'
    with open(input_file, 'r') as f: 
        inputs = [l for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)

