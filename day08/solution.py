# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from math import sqrt
from typing import Sequence


def distance(x: Sequence[int], y: Sequence[int]) -> float:
    return sqrt(sum((a - b) ** 2 for (a, b) in zip(x, y)))


def part01(inputs: list[str]) -> None:
    assert len(inputs) == 20 or len(inputs) == 1000
    N_PAIRS = 10 if len(inputs) == 20 else 1000

    junctions: list[list[int]] = [list(int(i) for i in l.split(",")) for l in inputs]
    adjacency_matrix: list[list[float]] = [
        [distance(box, other) for other in junctions] for box in junctions
    ]

    # make flat list of right hand side of matrix (past diagonal)
    values = dict()
    for i, row in enumerate(adjacency_matrix):
        for j, v in enumerate(row):
            if j > i:
                values[v] = (i, j)

    b = sorted(list(values.keys()), reverse=True)
    circuits = [set(values[v]) for v in b[-N_PAIRS:]]  # Wire up N closest junctions

    # Merge circuits iteratively until no merges are possible
    made_merges = True
    while made_merges:
        made_merges = False
        for i, _ in enumerate(circuits):
            j = i + 1
            while j < len(circuits):
                if circuits[i] & circuits[j]:  # has overlap
                    circuits[i] |= circuits[j]  # merge into left
                    circuits.pop(j)  # delete circuit j
                    made_merges = True
                else:
                    # only increment if len(circuits) doesn't change
                    j += 1

    final_connections = sorted(circuits, key=len)
    print(
        len(final_connections[-3])
        * len(final_connections[-2])
        * len(final_connections[-1])
    )
    return


def part02(inputs: list[str]) -> None:
    assert len(inputs) == 20 or len(inputs) == 1000
    N_PAIRS = 10 if len(inputs) == 20 else 1000

    junctions: list[list[int]] = [list(int(i) for i in l.split(",")) for l in inputs]
    adjacency_matrix: list[list[float]] = [
        [distance(box, other) for other in junctions] for box in junctions
    ]

    # make flat list of right hand side of matrix (past diagonal)
    values = dict()
    for i, row in enumerate(adjacency_matrix):
        for j, v in enumerate(row):
            if j > i:
                values[v] = (i, j)

    b = sorted(list(values.keys()), reverse=True)
    for n_connections in range(N_PAIRS, len(b)):
        circuits = [
            set(values[v]) for v in b[-n_connections:]
        ]  # Wire up N closest junctions
        made_merges = True
        while made_merges:
            made_merges = False
            i = 0
            while i < len(circuits):
                j = i + 1
                while j < len(circuits):
                    if circuits[i] & circuits[j]:  # has overlap
                        circuits[i] |= circuits[j]  # merge into left
                        circuits.pop(j)  # delete circuit j
                        made_merges = True
                    else:
                        # only increment if len(circuits) doesn't change
                        j += 1
                i += 1

        if len(circuits) == 1 and all(i in circuits[0] for i in range(len(junctions))):
            pair = values[b[-n_connections]]
            print(junctions[pair[0]][0] * junctions[pair[1]][0])
            break


if __name__ == "__main__":
    input_file = "sample.txt"
    input_file = "inputs.txt"
    with open(input_file, "r") as f:
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
