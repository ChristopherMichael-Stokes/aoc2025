# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from operator import itemgetter
from typing import Any, Iterable, TypeVar, Sequence

T = TypeVar('T')


def argsort(sequence: Iterable[T]) -> tuple[list[int], list[T]]: # (idx1, idx2,...), (val1, val2, ...)
        argsorted = [x for x in sorted(enumerate(sequence), key=itemgetter(1), reverse=True)]
        return zip(*argsorted) # type: ignore[invalid-return-type]


def part01(inputs: list[str]) -> None:
    joltages: list[int] = []

    for bank in inputs:
        idxs, vals = argsort(bank)
        # Two branches:
        # get the max, if it is at the end pick second max
        # then find the first max directly after it
        first_idx = idxs[1] if idxs[0] == len(bank) -1 else idxs[0]
        second_val = max(bank[first_idx+1:])
        joltages.append(int(bank[first_idx] + second_val))

    print(f'{joltages=}')
    print(f'{sum(joltages)=}')


def subset(sequence: Sequence[T], indices: list[int]) -> list[T]:
    return [sequence[i] for i in indices]


def part02(inputs: list[str]) -> None:
    # thinking of a backtracking solution?
    # start with 12 at the end turned on, then iteratively
    # move each idx from left to right until it hits its max
    # end when we've covered all 12 / can't move any more
    n_digits = 12
    joltages = []
    for bank in inputs:
        indices = list(range(len(bank) - n_digits, len(bank)))
        s = subset(bank, indices)
        for digit_idx in range(n_digits):
            start_idx = 0 if digit_idx == 0 else indices[digit_idx - 1] + 1
            search_space = bank[start_idx:len(bank)-(n_digits-digit_idx)+1]
            newval = max(search_space)
            newidx = search_space.index(newval) + start_idx
            indices[digit_idx] = newidx

        joltages.append(int(''.join(subset(bank, indices))))

    print(f'{joltages=}')
    print(f'{sum(joltages)=}')
    

if __name__=="__main__":
    input_file = 'sample.txt'
    input_file = 'inputs.txt'
    with open(input_file, 'r') as f: 
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
