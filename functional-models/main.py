# Copyright 2026 Cornell University
# released under MIT License
# author: Kevin Laeufer <laeufer@cornell.edu>

from pypatronus import BitVec, SignExt, ZeroExt, Slice
from fun import FunctionalModel, Transaction, serialize


def picorv32_pcpi_mul():
    """
    https://github.com/ekiwi/paso/blob/ad2bf83f420ca704ff0e76e7a583791a0e80a545/benchmarks/src/benchmarks/picorv32/PicoRV32Spec.scala#L8
    """
    m = FunctionalModel(name="picorv32_pcpi_mul")
    rs1, rs2 = BitVec("rs1_data", 32), BitVec("rs2_data", 32)
    m.transactions = [
        Transaction("pcpi_mul", [rs1, rs2], [("rd_data", rs1 * rs2)]),
        Transaction(
            "pcpi_mulh",
            [rs1, rs2],
            [("rd_data", Slice(63, 32, SignExt(32, rs1) * SignExt(32, rs2)))],
        ),
        Transaction(
            "pcpi_mulhu",
            [rs1, rs2],
            [("rd_data", Slice(63, 32, ZeroExt(32, rs1) * ZeroExt(32, rs2)))],
        ),
        Transaction(
            "pcpi_mulhsu",
            [rs1, rs2],
            [("rd_data", Slice(63, 32, SignExt(32, rs1) * ZeroExt(32, rs2)))],
        ),
    ]
    return m


def main():
    m = picorv32_pcpi_mul()
    print(m)
    serialize(m, "picorv32_pcpi_mul.json")


if __name__ == "__main__":
    main()
