# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from bisect import bisect_left
from itertools import pairwise
from operator import itemgetter


def parse_inputs(inputs: list[str]) -> tuple[list[tuple[int, int]], list[int]]:
    ranges: list[tuple[int, int]] = []
    stock: list[int] = []

    for line in inputs:
        if '-' in line:
            start, end = line.split('-')
            ranges.append((int(start), int(end)))
        else:
            stock.append(int(line))

    ranges = sorted(ranges, key=itemgetter(0))
    return ranges, stock


def part01(inputs: list[str]) -> None:
    ranges, stock = parse_inputs(inputs)
    fresh_stock: list[int] = []

    for fruit in stock:
        insertion = bisect_left(ranges, fruit, key=itemgetter(0))
        insertion_ranges = (ranges[i % len(ranges)] for i in (insertion - 1, insertion, insertion + 1))
        if any(r[0] <= fruit <= r[1] for r in insertion_ranges):
            fresh_stock.append(fruit)

    print(f'{len(fresh_stock)=}')


def part02(inputs: list[str]) -> None:
    ranges, _ = parse_inputs(inputs)
    merged_ranges = [ranges[0]]

    # iteratively work out merges
    while ranges:
        r1, r2 = merged_ranges.pop(-1), ranges.pop(0)

        if r1[0] <= r2[0] <= r1[1]:
            merged_ranges.append((r1[0], max(r1[1], r2[1])))
        else:
            merged_ranges.extend([r1, r2])

    valid_count = 0
    for (a, b) in merged_ranges:
        valid_count += (b + 1) - a

    print(f'{valid_count=}')


if __name__=="__main__":
    input_file = 'sample.txt'
    input_file = 'inputs.txt'
    with open(input_file, 'r') as f: 
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)

