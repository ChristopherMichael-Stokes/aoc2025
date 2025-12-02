# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
from typing import Generator


def is_invalid(x: int) -> bool:
    x_str = str(x)
    i = len(x_str) // 2
    return x_str[:i] == x_str[i:]
        

def next_code(inputs: str) -> Generator[int, None, None]:
    for search_space in inputs.split(','):
        y0, y1 = search_space.split('-')
        for x in range(int(y0), int(y1)+1):
            yield x


def part01(inputs: str) -> None:
    invalid_codes: list[int] = []
    for x in next_code(inputs):
        if is_invalid(x):
            invalid_codes.append(x)

    # print(invalid_codes)
    print(f'{len(invalid_codes)=}')
    print(f'{sum(invalid_codes)=}')
                 

def is_invalid_recursive(x: str, seq_len: int) -> bool:
    if seq_len == 0: return False 

    if x[:seq_len] * (len(x) // seq_len) == x:
        return True
    else:
        return is_invalid_recursive(x, seq_len - 1)


def part02(inputs: str) -> None:
    invalid_codes: list[int] = []
    for x in next_code(inputs):
        if is_invalid_recursive(str(x), len(str(x)) // 2):
            invalid_codes.append(x)

    # print(invalid_codes)
    print(f'{len(invalid_codes)=}')
    print(f'{sum(invalid_codes)=}')


if __name__=="__main__":
    input_file = 'sample.txt'
    input_file = 'inputs.txt'
    with open(input_file, 'r') as f: 
        inputs = ''.join([l.strip() for l in f.readlines() if not l.isspace()])

    part01(inputs)
    part02(inputs)
