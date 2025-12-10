# /// script
# requires-python = ">=3.14"
# dependencies = []
# ///
def part01(inputs: list[str]) -> None:
    pass


def part02(inputs: list[str]) -> None:
    pass   


if __name__=="__main__":
    input_file = 'inputs.txt'
    input_file = 'sample.txt'
    with open(input_file, 'r') as f: 
        inputs = [l.strip() for l in f.readlines() if not l.isspace()]

    part01(inputs)
    part02(inputs)
