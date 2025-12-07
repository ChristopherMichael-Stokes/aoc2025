# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from collections import defaultdict
from itertools import pairwise


SPLITTER="^"
EMPTY="."
START="S"
BEAM = "|"


def part01(inputs: list[str]) -> None:
    beam_path = [set() for _ in range(len(inputs))]
    beam_path[1] = {inputs[0].find(START)}
    n_beam_splits = 0

    for row_idx, line in enumerate(inputs):
        if row_idx < 2:
            continue
        
        splitter_pos = {i for (i,v) in enumerate(line) if v == SPLITTER}

        beam_proposals = []
        for col_idx in beam_path[row_idx - 1]:
            if col_idx in splitter_pos:
                beam_proposals.extend([col_idx - 1, col_idx + 1])
            else:
                beam_proposals.append(col_idx)

        beam_actual = set(beam_proposals) - splitter_pos
        
        # Count a split as whether there is a beam above and either left or right of a splitter
        for sp in splitter_pos:
            if sp in beam_path[row_idx - 1] and (sp - 1 in beam_actual or sp + 1 in beam_actual):
                n_beam_splits += 1

        beam_path[row_idx] = beam_actual

    print(f"{n_beam_splits=}")


def part02(inputs: list[str], visualise: bool = False) -> None:
    enum_map = {EMPTY: 0, SPLITTER: -1, START: 1}
    grid = [[enum_map[c] for c in line] for line in inputs]

    # Iterative approach, mark each beam with how many routes lead to it
    for current_row, next_row in pairwise(grid):
        for idx, v in enumerate(current_row):
            if v > 0: # We're on a beam
                # Add the value directly below if clear
                if next_row[idx] >= 0:
                    next_row[idx] += v
                # Add value below left & right if above a splitter
                elif next_row[idx] == enum_map[SPLITTER]:
                    next_row[idx - 1] += v
                    next_row[idx + 1] += v

    if visualise:
        for line in grid:
            for v in line:
                if v != -1:
                    print(str(v).rjust(4, ' '), end="")
                else:
                    print("  ^^", end="")
            print()

    n_timelines = sum(grid[-1]) 
    print(f"{n_timelines=}")




if __name__=="__main__":
    input_file = 'sample.txt'
    input_file = 'inputs.txt'
    with open(input_file, 'r') as f: 
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    # part02(inputs, True)
    part02(inputs)

