# Copyright 2026 Cornell University
# released under MIT License
# author: Kevin Laeufer <laeufer@cornell.edu>

from pypatronus import BitVec, SignExt, ZeroExt, Slice, Update, If, Array, BitVecVal
from fun import FunctionalModel, Method, serialize, Sim


def picorv32_pcpi_mul():
    """
    https://github.com/ekiwi/paso/blob/ad2bf83f420ca704ff0e76e7a583791a0e80a545/benchmarks/src/benchmarks/picorv32/PicoRV32Spec.scala#L8
    """
    m = FunctionalModel(name="picorv32_pcpi_mul")
    rs1, rs2 = BitVec("rs1_data", 32), BitVec("rs2_data", 32)
    m.methods = [
        Method("pcpi_mul", [rs1, rs2], [("rd_data", rs1 * rs2)]),
        Method(
            "pcpi_mulh",
            [rs1, rs2],
            [("rd_data", Slice(63, 32, SignExt(32, rs1) * SignExt(32, rs2)))],
        ),
        Method(
            "pcpi_mulhu",
            [rs1, rs2],
            [("rd_data", Slice(63, 32, ZeroExt(32, rs1) * ZeroExt(32, rs2)))],
        ),
        Method(
            "pcpi_mulhsu",
            [rs1, rs2],
            [("rd_data", Slice(63, 32, SignExt(32, rs1) * ZeroExt(32, rs2)))],
        ),
        Method("pcpi_mul_reset"),
        Method("idle"),
    ]
    return m


def fifo(data_width: int, num_elements: int, push_pop: bool = False):
    """https://github.com/ekiwi/paso/blob/ad2bf83f420ca704ff0e76e7a583791a0e80a545/benchmarks/src/benchmarks/fifo/FifoSpec.scala"""
    counter_width = 12
    assert num_elements < ((1 << (counter_width - 1)) - 1)
    mem = Array("mem", counter_width, data_width)
    count = BitVec("count", counter_width)
    read = BitVec("read", counter_width)
    m = FunctionalModel(name="fifo", states=[mem, count, read])
    num_elements_bv = BitVecVal(num_elements, counter_width)
    full = count.equals(num_elements_bv)
    zero = BitVecVal(0, counter_width)
    empty = count.equals(zero)
    input = BitVec("input", data_width)

    non_wrap = count + read
    write_adr = If(non_wrap < num_elements_bv, non_wrap, non_wrap - num_elements_bv)
    read_plus_one = read + BitVecVal(1, counter_width)
    read_incr = If(
        read_plus_one.equals(num_elements_bv),
        zero,
        read_plus_one,
    )

    m.methods = [
        Method(
            "push",
            [input],
            [],
            [
                Update(mem, write_adr, input),  # mem
                count + BitVecVal(1, counter_width),  # count
                read,  # read
            ],
            ~full,
        ),
        Method(
            "pop",
            [],
            [("output", mem[read])],
            [
                mem,  # mem
                count - BitVecVal(1, counter_width),  # count
                read_incr,  # read
            ],
            ~empty,
        ),
        Method("reset", nexts=[mem, zero, zero]),
        Method("idle"),
    ]
    if push_pop:
        m.methods.append(
            Method(
                "push_pop",
                [input],
                [("output", mem[read])],
                [
                    Update(mem, write_adr, input),  # mem
                    count,  # count
                    read_incr,  # read
                ],
            ),
        )
    return m


def test_fifo(m: FunctionalModel, num_elements: int, push_pop: bool = False):
    sim = Sim(m)
    # sim.push(123)
    # assert sim.pop() == 123
    pass  # TODO: implement simulator for testing


def main():
    serialize(picorv32_pcpi_mul(), "picorv32_pcpi_mul.json")
    params = [
        {"data_width": 32, "num_elements": 8},
        {"data_width": 32, "num_elements": 16},
        {"data_width": 32, "num_elements": 128},
    ]
    for p in params:
        file_name = "fifo_" + "_".join(f"{k}={v}" for k, v in p.items()) + ".json"
        m = fifo(**p)
        test_fifo(m, num_elements=p["num_elements"])
        serialize(m, file_name)


if __name__ == "__main__":
    main()
