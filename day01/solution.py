# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from operator import sub, add

DIAL_MAX = 99
DIAL_START = 50

def part01(inputs: list[str]) -> None:
    dial_position = DIAL_START
    zero_count = 0

    for instruction in inputs:
        d, v = instruction[0], int(instruction[1:])
        op = sub if d == 'L' else add

        dial_position = op(dial_position, v) % (DIAL_MAX + 1)
        if dial_position == 0:
            zero_count += 1

    print(f"{dial_position=}")
    print(f"{zero_count=}")


def part02(inputs: list[str]) -> None:
    dial_position = DIAL_START
    zero_count = 0

    for instruction in inputs:
        d, v = instruction[0], int(instruction[1:])
        op = sub if d == 'L' else add

        for _ in range(v):
            dial_position = op(dial_position, 1) % (DIAL_MAX + 1)
            if dial_position == 0:
                zero_count += 1

        # TODO: efficient implementation leftovers
        # zero_count += abs(dial_pos) // (DIAL_MAX + 1)
        # dial_position = dial_pos % (DIAL_MAX + 1)
        # zero_count += dial_pos < 0 and dial_pos > -100 # If we've wrapped left a single iteration worth less than 100
        # zero_count += dial_pos < 0
        # print(f"{d}, {v}, {dial_pos}, {dial_position}, {zero_count}")

    print(f"{dial_position=}")
    print(f"{zero_count=}")



if __name__=="__main__":
    input_file = 'sample.txt'
    input_file = 'inputs.txt'
    with open(input_file, 'r') as f: 
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
