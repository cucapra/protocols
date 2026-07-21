# Checked-in test catalog. Hand-maintained source of truth.
# Consumed by scripts/generate_runt_configs.py.
#
# TX_CASES are keyed by their .tx path. BI_CASES are keyed by a unique id

TX_CASES = {
    "examples/picorv32/unsigned_mul.tx": {
        "protocol": "examples/picorv32/pcpi_mul.prot",
        "verilog": ("examples/picorv32/picorv32.v",),
        "top": "picorv32_pcpi_mul",
        "expect": "pass",
    },
    "examples/serv/serv_regfile.tx": {
        "protocol": "examples/serv/serv_regfile.prot",
        "verilog": ("examples/serv/rtl/serv_regfile.v",),
        "expect": "pass",
    },
    "examples/tinyaes128/aes128.tx": {
        "protocol": "examples/tinyaes128/aes128.prot",
        "verilog": ("examples/tinyaes128/aes_128.v",),
        "top": "aes_128",
        "expect": "pass",
    },
    "examples/wishbone/4.8_constant_address_burst.tx": {
        "protocol": "examples/wishbone/wishbone.prot",
        "verilog": ("examples/wishbone/rtl/dut.v", "examples/wishbone/rtl/tb.v"),
        "top": "tb",
        "expect": "pass",
    },
    "examples/wishbone/4.?_incremental_address_burst.tx": {
        "protocol": "examples/wishbone/wishbone.prot",
        "verilog": ("examples/wishbone/rtl/dut.v", "examples/wishbone/rtl/tb.v"),
        "top": "tb",
        "expect": "pass",
    },
    "examples/wishbone/4.?_incremental_address_burst_wrap.tx": {
        "protocol": "examples/wishbone/wishbone.prot",
        "verilog": ("examples/wishbone/rtl/dut.v", "examples/wishbone/rtl/tb.v"),
        "top": "tb",
        "expect": "pass",
    },
    "tests/adders/adder_d0/add_combinational.tx": {
        "protocol": "tests/adders/adder_d0/add_d0.prot",
        "verilog": ("tests/adders/adder_d0/add_d0.v",),
        "expect": "pass",
    },
    "tests/adders/adder_d0/illegal_assignment.tx": {
        "protocol": "tests/adders/adder_d0/add_d0.prot",
        "verilog": ("tests/adders/adder_d0/add_d0.v",),
        "expect": "comb_dependency",
    },
    "tests/adders/adder_d0/illegal_observation_assertion.tx": {
        "protocol": "tests/adders/adder_d0/add_d0.prot",
        "verilog": ("tests/adders/adder_d0/add_d0.v",),
        "expect": "comb_dependency",
    },
    "tests/adders/adder_d0/illegal_observation_conditional.tx": {
        "protocol": "tests/adders/adder_d0/add_d0.prot",
        "verilog": ("tests/adders/adder_d0/add_d0.v",),
        "expect": "comb_dependency",
    },
    "tests/adders/adder_d1/add_incorrect.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "assignment_conflict",
    },
    "tests/adders/adder_d1/add_incorrect_implicit.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "assignment_conflict",
    },
    "tests/adders/adder_d1/add_multitrace.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "assertion_mismatch",
    },
    "tests/adders/adder_d1/add_multitrace_successful.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "pass",
    },
    "tests/adders/adder_d1/both_threads_fail.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "assertion_mismatch",
    },
    "tests/adders/adder_d1/both_threads_pass.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "pass",
    },
    "tests/adders/adder_d1/assign_after_observation.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "comb_dependency",
    },
    "tests/adders/adder_d1/didnt_end_in_step.tx": {
        "protocol": "tests/adders/adder_d1/didnt_end_in_step.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "fork_protocol_error",
        "extra_args": ("--skip-static-step-fork-checks",),
    },
    "tests/adders/adder_d1/double_fork_error.tx": {
        "protocol": "tests/adders/adder_d1/double_fork_error.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "fork_protocol_error",
        "extra_args": ("--skip-static-step-fork-checks",),
    },
    "tests/adders/adder_d1/first_fail_second_norun.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "assertion_mismatch",
    },
    "tests/adders/adder_d1/first_thread_fails.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "assertion_mismatch",
    },
    "tests/adders/adder_d1/fork_before_step_error.tx": {
        "protocol": "tests/adders/adder_d1/fork_before_step_error.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "fork_protocol_error",
        "extra_args": ("--skip-static-step-fork-checks",),
    },
    "tests/adders/adder_d1/second_thread_fails.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "assertion_mismatch",
    },
    "tests/adders/adder_d1/wait_and_add_correct.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "pass",
    },
    "tests/adders/adder_d1/wait_and_add_incorrect_implicit.tx": {
        "protocol": "tests/adders/adder_d1/add_d1.prot",
        "verilog": ("tests/adders/adder_d1/add_d1.v",),
        "expect": "assignment_conflict",
    },
    "tests/adders/adder_d2/both_threads_pass.tx": {
        "protocol": "tests/adders/adder_d2/add_d2.prot",
        "verilog": ("tests/adders/adder_d2/add_d2.v",),
        "expect": "pass",
        "max_steps": 4,
    },
    "tests/adders/adder_d2/no_dontcare_conflict.tx": {
        "protocol": "tests/adders/adder_d2/no_dontcare_conflict.prot",
        "verilog": ("tests/adders/adder_d2/add_d2.v",),
        "expect": "assignment_conflict",
    },
    "tests/alus/alu_d1.tx": {
        "protocol": "tests/alus/alu_d1.prot",
        "verilog": ("tests/alus/alu_d1.v",),
        "top": "alu_d1",
        "expect": "pass",
    },
    "tests/alus/alu_d2.tx": {
        "protocol": "tests/alus/alu_d2.prot",
        "verilog": ("tests/alus/alu_d2.v",),
        "top": "alu_d2",
        "expect": "pass",
    },
    "tests/bounded_ready_valid/toy_reciever_0.tx": {
        "protocol": "tests/bounded_ready_valid/bounded_rv.prot",
        "verilog": ("tests/bounded_ready_valid/toy_receiver_0.v",),
        "expect": "pass",
    },
    "tests/bounded_ready_valid/toy_reciever_1.tx": {
        "protocol": "tests/bounded_ready_valid/bounded_rv.prot",
        "verilog": ("tests/bounded_ready_valid/toy_receiver_1.v",),
        "expect": "pass",
    },
    "tests/bounded_ready_valid/toy_reciever_2.tx": {
        "protocol": "tests/bounded_ready_valid/bounded_rv.prot",
        "verilog": ("tests/bounded_ready_valid/toy_receiver_2.v",),
        "expect": "pass",
    },
    "tests/bounded_ready_valid/toy_reciever_3.tx": {
        "protocol": "tests/bounded_ready_valid/bounded_rv.prot",
        "verilog": ("tests/bounded_ready_valid/toy_receiver_3.v",),
        "expect": "assertion_mismatch",
    },
    "tests/brave_new_world/bit_truncation/bit_truncation_fft_bug.tx": {
        "protocol": "tests/brave_new_world/bit_truncation/bit_truncation_fft.prot",
        "verilog": ("tests/brave_new_world/bit_truncation/bit_truncation_fft_bug.v",),
        "top": "bit_truncation_fft_bug",
        "expect": "assertion_mismatch",
    },
    "tests/brave_new_world/bit_truncation/bit_truncation_fft_fix.tx": {
        "protocol": "tests/brave_new_world/bit_truncation/bit_truncation_fft.prot",
        "verilog": ("tests/brave_new_world/bit_truncation/bit_truncation_fft_fix.v",),
        "top": "round11_rne_unsigned_fixed",
        "expect": "pass",
    },
    "tests/brave_new_world/bit_truncation/bit_truncation_sha_bug.tx": {
        "protocol": "tests/brave_new_world/bit_truncation/bit_truncation_sha.prot",
        "verilog": ("tests/brave_new_world/bit_truncation/bit_truncation_sha_bug.v",),
        "top": "bit_truncation_sha_bug",
        "expect": "assertion_mismatch",
    },
    "tests/brave_new_world/bit_truncation/bit_truncation_sha_fix.tx": {
        "protocol": "tests/brave_new_world/bit_truncation/bit_truncation_sha.prot",
        "verilog": ("tests/brave_new_world/bit_truncation/bit_truncation_sha_fix.v",),
        "top": "bit_truncation_sha_fixed",
        "expect": "pass",
    },
    "tests/brave_new_world/failure_to_update/ftu_sha_bug.tx": {
        "protocol": "tests/brave_new_world/failure_to_update/ftu_sha.prot",
        "verilog": ("tests/brave_new_world/failure_to_update/ftu_sha_bug.v",),
        "top": "fsm_update_buggy",
        "expect": "assertion_mismatch",
    },
    "tests/brave_new_world/failure_to_update/ftu_sha_fix.tx": {
        "protocol": "tests/brave_new_world/failure_to_update/ftu_sha.prot",
        "verilog": ("tests/brave_new_world/failure_to_update/ftu_sha_fix.v",),
        "top": "fsm_update_fixed_gated",
        "expect": "pass",
    },
    "tests/brave_new_world/signal_asynchrony/signal_async_bug.tx": {
        "protocol": "tests/brave_new_world/signal_asynchrony/signal_async.prot",
        "verilog": ("tests/brave_new_world/signal_asynchrony/signal_async_bug.v",),
        "top": "signal_async_bug",
        "expect": "assertion_mismatch",
    },
    "tests/brave_new_world/signal_asynchrony/signal_async_fix.tx": {
        "protocol": "tests/brave_new_world/signal_asynchrony/signal_async.prot",
        "verilog": ("tests/brave_new_world/signal_asynchrony/signal_async_fix.v",),
        "top": "signal_async_fix",
        "expect": "pass",
    },
    "tests/brave_new_world/use_without_valid/use_without_valid_bug.tx": {
        "protocol": "tests/brave_new_world/use_without_valid/use_without_valid.prot",
        "verilog": ("tests/brave_new_world/use_without_valid/use_without_valid_bug.v",),
        "top": "use_without_valid_bug",
        "expect": "assertion_mismatch",
    },
    "tests/brave_new_world/use_without_valid/use_without_valid_fix.tx": {
        "protocol": "tests/brave_new_world/use_without_valid/use_without_valid.prot",
        "verilog": ("tests/brave_new_world/use_without_valid/use_without_valid_fix.v",),
        "top": "use_without_valid_fix",
        "expect": "pass",
    },
    "tests/counters/counter.tx": {
        "protocol": "tests/counters/counter.prot",
        "verilog": ("tests/counters/counter.v",),
        "expect": "pass",
    },
    "tests/fifo/fifo.tx": {
        "protocol": "tests/fifo/fifo.prot",
        "verilog": (
            "tests/fifo/bsg_mem_1rw_sync.v",
            "tests/fifo/bsg_mem_1rw_sync_synth.v",
            "tests/fifo/bsg_circular_ptr.v",
            "tests/fifo/bsg_fifo_1rw_large.v",
            "tests/fifo/fifo_wrapper.v",
        ),
        "top": "fifo_wrapper",
        "expect": "pass",
    },
    "tests/fifo/pop_before_push_fail.tx": {
        "protocol": "tests/fifo/fifo.prot",
        "verilog": (
            "tests/fifo/bsg_mem_1rw_sync.v",
            "tests/fifo/bsg_mem_1rw_sync_synth.v",
            "tests/fifo/bsg_circular_ptr.v",
            "tests/fifo/bsg_fifo_1rw_large.v",
            "tests/fifo/fifo_wrapper.v",
        ),
        "top": "fifo_wrapper",
        "expect": "assertion_mismatch",
    },
    "tests/fifo/pop_empty_fail.tx": {
        "protocol": "tests/fifo/fifo.prot",
        "verilog": (
            "tests/fifo/bsg_mem_1rw_sync.v",
            "tests/fifo/bsg_mem_1rw_sync_synth.v",
            "tests/fifo/bsg_circular_ptr.v",
            "tests/fifo/bsg_fifo_1rw_large.v",
            "tests/fifo/fifo_wrapper.v",
        ),
        "top": "fifo_wrapper",
        "expect": "assertion_mismatch",
    },
    "tests/fifo/push_pop_conflict.tx": {
        "protocol": "tests/fifo/fifo.prot",
        "verilog": (
            "tests/fifo/bsg_mem_1rw_sync.v",
            "tests/fifo/bsg_mem_1rw_sync_synth.v",
            "tests/fifo/bsg_circular_ptr.v",
            "tests/fifo/bsg_fifo_1rw_large.v",
            "tests/fifo/fifo_wrapper.v",
        ),
        "top": "fifo_wrapper",
        "expect": "assertion_mismatch",
    },
    "tests/fifo/push_pop_identity_ok.tx": {
        "protocol": "tests/fifo/fifo.prot",
        "verilog": (
            "tests/fifo/bsg_mem_1rw_sync.v",
            "tests/fifo/bsg_mem_1rw_sync_synth.v",
            "tests/fifo/bsg_circular_ptr.v",
            "tests/fifo/bsg_fifo_1rw_large.v",
            "tests/fifo/fifo_wrapper.v",
        ),
        "top": "fifo_wrapper",
        "expect": "pass",
    },
    "tests/identities/dual_identity_d0/dual_identity_d0_combdep.tx": {
        "protocol": "tests/identities/dual_identity_d0/dual_identity_d0.prot",
        "verilog": ("tests/identities/dual_identity_d0/dual_identity_d0.v",),
        "expect": "comb_dependency",
    },
    "tests/identities/dual_identity_d1/dual_identity_d1.tx": {
        "protocol": "tests/identities/dual_identity_d1/dual_identity_d1.prot",
        "verilog": ("tests/identities/dual_identity_d1/dual_identity_d1.v",),
        "expect": "static_well_formedness",
    },
    "tests/identities/identity_d0/passthrough_combdep.tx": {
        "protocol": "tests/identities/identity_d0/identity_d0.prot",
        "verilog": ("tests/identities/identity_d0/identity_d0.v",),
        "expect": "pass",
    },
    "tests/identities/identity_d1/explicit_fork.tx": {
        "protocol": "tests/identities/identity_d1/identity_d1.prot",
        "verilog": ("tests/identities/identity_d1/identity_d1.v",),
        "expect": "assertion_mismatch",
    },
    "tests/identities/identity_d1/slicing_err.tx": {
        "protocol": "tests/identities/identity_d1/slicing_err.prot",
        "verilog": ("tests/identities/identity_d1/identity_d1.v",),
        "expect": "static_type_error",
    },
    "tests/identities/identity_d1/slicing_invalid.tx": {
        "protocol": "tests/identities/identity_d1/slicing_invalid.prot",
        "verilog": ("tests/identities/identity_d1/identity_d1.v",),
        "expect": "static_type_error",
    },
    "tests/identities/identity_d1/slicing_ok.tx": {
        "protocol": "tests/identities/identity_d1/identity_d1.prot",
        "verilog": ("tests/identities/identity_d1/identity_d1.v",),
        "expect": "pass",
    },
    "tests/identities/identity_d2/single_thread_passes.tx": {
        "protocol": "tests/identities/identity_d2/identity_d2.prot",
        "verilog": ("tests/identities/identity_d2/identity_d2.v",),
        "expect": "pass",
    },
    "tests/identities/identity_d2/two_assignments_same_value.tx": {
        "protocol": "tests/identities/identity_d2/identity_d2.prot",
        "verilog": ("tests/identities/identity_d2/identity_d2.v",),
        "expect": "pass",
    },
    "tests/identities/identity_d2/two_different_assignments_error.tx": {
        "protocol": "tests/identities/identity_d2/identity_d2.prot",
        "verilog": ("tests/identities/identity_d2/identity_d2.v",),
        "expect": "assignment_conflict",
    },
    "tests/identities/identity_d2/two_fork_err.tx": {
        "protocol": "tests/identities/identity_d2/two_fork_err.prot",
        "verilog": ("tests/identities/identity_d2/identity_d2.v",),
        "expect": "fork_protocol_error",
        "extra_args": ("--skip-static-step-fork-checks",),
    },
    "tests/identities/identity_d2/two_fork_ill_formed.tx": {
        "protocol": "tests/identities/identity_d2/two_fork_ill_formed.prot",
        "verilog": ("tests/identities/identity_d2/identity_d2.v",),
        "expect": "static_well_formedness",
    },
    "tests/inverters/inverter_d0.tx": {
        "protocol": "tests/inverters/inverter_d0.prot",
        "verilog": ("tests/inverters/inverter_d0.v",),
        "expect": "comb_dependency",
    },
    "tests/multi/multi0/multi0.tx": {
        "protocol": "tests/multi/multi0/multi0.prot",
        "verilog": ("tests/multi/multi0/multi0.v",),
        "top": "multi0",
        "expect": "pass",
    },
    "tests/multi/multi0keep/multi0keep.tx": {
        "protocol": "tests/multi/multi0keep/multi0keep.prot",
        "verilog": ("tests/multi/multi0keep/multi0keep.v",),
        "top": "multi0keep",
        "expect": "pass",
    },
    "tests/multi/multi0keep2const/multi0keep2const.tx": {
        "protocol": "tests/multi/multi0keep2const/multi0keep2const.prot",
        "verilog": (
            "tests/multi/multi0keep2const/multi0keep2const.v",
            "tests/multi/multi0keep/multi0keep.v",
        ),
        "top": "multi0keep2const",
        "expect": "pass",
    },
    "tests/multi/multi2const/multi2const.tx": {
        "protocol": "tests/multi/multi2const/multi2const.prot",
        "verilog": (
            "tests/multi/multi2const/multi2const.v",
            "tests/multi/multi0/multi0.v",
        ),
        "top": "multi2const",
        "expect": "pass",
    },
    "tests/multi/multi2multi/multi2multi.tx": {
        "protocol": "tests/multi/multi2multi/multi2multi.prot",
        "verilog": (
            "tests/multi/multi2multi/multi2multi.v",
            "tests/multi/multi0/multi0.v",
        ),
        "top": "multi2multi",
        "expect": "pass",
    },
    "tests/multi/multi_data/multi_data.tx": {
        "protocol": "tests/multi/multi_data/multi_data.prot",
        "verilog": ("tests/multi/multi_data/multi_data.v",),
        "expect": "pass",
    },
    "tests/multipliers/mult_d2/both_threads_fail.tx": {
        "protocol": "tests/multipliers/mult_d2/mult_d2.prot",
        "verilog": ("tests/multipliers/mult_d2/mult_d2.v",),
        "expect": "assertion_mismatch",
    },
    "tests/multipliers/mult_d2/both_threads_pass.tx": {
        "protocol": "tests/multipliers/mult_d2/mult_d2.prot",
        "verilog": ("tests/multipliers/mult_d2/mult_d2.v",),
        "expect": "pass",
    },
    "tests/multipliers/mult_d2/first_thread_fails.tx": {
        "protocol": "tests/multipliers/mult_d2/mult_d2.prot",
        "verilog": ("tests/multipliers/mult_d2/mult_d2.v",),
        "expect": "assertion_mismatch",
    },
    "tests/multipliers/mult_d2/second_thread_fails.tx": {
        "protocol": "tests/multipliers/mult_d2/mult_d2.prot",
        "verilog": ("tests/multipliers/mult_d2/mult_d2.v",),
        "expect": "assertion_mismatch",
    },
    "tests/picorv32/unsigned_mul_no_reset.tx": {
        "protocol": "tests/picorv32/pcpi_mul_no_reset.prot",
        "verilog": ("examples/picorv32/picorv32.v",),
        "top": "picorv32_pcpi_mul",
        "expect": "max_steps",
        "max_steps": 200,
    },
    "tests/picorv32/unsigned_mul_no_reset_thread_assignment_persistence.tx": {
        "protocol": "tests/picorv32/pcpi_mul_no_reset.prot",
        "verilog": ("examples/picorv32/picorv32.v",),
        "top": "picorv32_pcpi_mul",
        "expect": "max_steps",
        "max_steps": 200,
    },
    "tests/wishbone/wishbone.tx": {
        "protocol": "tests/wishbone/wishbone.prot",
        "verilog": ("tests/wishbone/reqwalker.v",),
        "top": "reqwalker",
        "expect": "pass",
    },
}

BI_CASES = {
    "tests.adders.add_d1": {
        "protocol": "tests/adders/add_d1.prot",
        "wave": "tests/adders/add_d1.fst",
        "instances": ("add_d1:Adder",),
        "expect": "pass",
    },
    "tests.adders.add_d2": {
        "protocol": "tests/adders/add_d2.prot",
        "wave": "tests/adders/add_d2.fst",
        "instances": ("add_d2:Adder",),
        "expect": "pass",
    },
    "tests.adders.add_var_cyc": {
        "protocol": "tests/adders/add_var_cyc.prot",
        "wave": "tests/adders/loop_with_assigns.fst",
        "instances": ("add_d1:Adder",),
        "expect": "pass",
    },
    "tests.alus.alu_d1.bi": {
        "protocol": "tests/alus/alu_d1.bi.prot",
        "wave": "tests/alus/alu_d1.fst",
        "instances": ("alu_d1:ALU",),
        "expect": "pass",
    },
    "tests.alus.alu_d2.bi": {
        "protocol": "tests/alus/alu_d2.bi.prot",
        "wave": "tests/alus/alu_d2.fst",
        "instances": ("alu_d2:ALU",),
        "expect": "pass",
    },
    "tests.brave_new_world_francis.bit_truncation_fft": {
        "protocol": "tests/brave_new_world_francis/bit_truncation_fft.prot",
        "wave": "tests/brave_new_world_francis/bit_truncation_fft.fst",
        "instances": ("round11_rne_unsigned_fixed:BitTruncationFFT",),
        "expect": "pass",
    },
    "tests.brave_new_world_francis.bit_truncation_sha": {
        "protocol": "tests/brave_new_world_francis/bit_truncation_sha.prot",
        "wave": "tests/brave_new_world_francis/bit_truncation_sha.fst",
        "instances": ("bit_truncation_sha_fixed:bit_truncation_sha",),
        "expect": "pass",
    },
    "tests.brave_new_world_francis.ftu_sha": {
        "protocol": "tests/brave_new_world_francis/ftu_sha.prot",
        "wave": "tests/brave_new_world_francis/ftu_sha.fst",
        "instances": ("fsm_update_fixed_gated:FailureToUpdateSHA",),
        "expect": "pass",
    },
    "tests.brave_new_world_francis.signal_async": {
        "protocol": "tests/brave_new_world_francis/signal_async.prot",
        "wave": "tests/brave_new_world_francis/signal_async.fst",
        "instances": ("signal_async_fix:SignalAsyncSpec",),
        "expect": "pass",
    },
    "tests.brave_new_world_francis.use_without_valid": {
        "protocol": "tests/brave_new_world_francis/use_without_valid.prot",
        "wave": "tests/brave_new_world_francis/use_without_valid.fst",
        "instances": ("use_without_valid_fix:UseWithoutValid",),
        "expect": "pass",
    },
    "tests.ethmac.ethmac_wishbone_manager": {
        "protocol": "tests/ethmac/ethmac_wishbone_manager.prot",
        "instances": ("tb_ethernet:WBManager",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "tb_ethernet.wb_clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.ethmac.ethmac_wishbone_subordinate": {
        "protocol": "tests/ethmac/ethmac_wishbone_subordinate.prot",
        "instances": ("tb_ethernet:WBSubordinate",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "tb_ethernet.wb_clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fifo.fifo.bi": {
        "protocol": "tests/fifo/fifo.bi.prot",
        "wave": "tests/fifo/fifo.fst",
        "instances": ("fifo_wrapper:Fifo",),
        "expect": "pass",
    },
    "tests.fifo.push_pop_identity": {
        "protocol": "tests/fifo/push_pop_identity.prot",
        "wave": "tests/fifo/push_pop_identity.fst",
        "instances": ("fifo_wrapper:Fifo",),
        "expect": "pass",
    },
    "tests.fpga-debugging.axi-burst-s4.s4_buggy": {
        "protocol": "tests/fpga-debugging/axi-burst-s4/s4_buggy.prot",
        "wave": "tests/fpga-debugging/axi-burst-s4/s4_buggy.vcd",
        "instances": ("TOP.test_l2_cache_wait_state.axi_bus:WriteSubordinate",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "TOP.test_l2_cache_wait_state.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axi-burst-s4.s4_fixed": {
        "protocol": "tests/fpga-debugging/axi-burst-s4/s4_fixed.prot",
        "wave": "tests/fpga-debugging/axi-burst-s4/s4_fixed.vcd",
        "instances": ("TOP.test_l2_cache_wait_state.axi_bus:WriteSubordinate",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.test_l2_cache_wait_state.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axi-lite-s1.s1_buggy": {
        "protocol": "tests/fpga-debugging/axi-lite-s1/s1_buggy.prot",
        "wave": "tests/fpga-debugging/axi-lite-s1/s1_buggy_workload2.vcd",
        "instances": (
            "TOP.testbench.UUT:WriteSubordinate",
            "TOP.testbench.UUT:ReadSubordinate",
        ),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "TOP.testbench.UUT.S_AXI_ACLK",
            "--show-waveform-time",
            "--time-unit",
            "ns",
            "--include-idle",
        ),
    },
    "tests.fpga-debugging.axi-lite-s1.s1_buggy_workload_1": {
        "protocol": "tests/fpga-debugging/axi-lite-s1/s1_buggy_workload_1.prot",
        "wave": "tests/fpga-debugging/axi-lite-s1/s1_buggy_workload1.vcd",
        "instances": (
            "TOP.testbench.UUT:WriteSubordinate",
            "TOP.testbench.UUT:ReadSubordinate",
        ),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "TOP.testbench.UUT.S_AXI_ACLK",
            "--show-waveform-time",
            "--time-unit",
            "ns",
            "--include-idle",
        ),
    },
    "tests.fpga-debugging.axi-lite-s1.s1_fixed": {
        "protocol": "tests/fpga-debugging/axi-lite-s1/s1_fixed.prot",
        "wave": "tests/fpga-debugging/axi-lite-s1/s1_fixed_workload2.vcd",
        "instances": (
            "TOP.testbench.UUT:WriteSubordinate",
            "TOP.testbench.UUT:ReadSubordinate",
        ),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.testbench.UUT.S_AXI_ACLK",
            "--show-waveform-time",
            "--time-unit",
            "ns",
            "--include-idle",
        ),
    },
    "tests.fpga-debugging.axi-lite-s1.s1_fixed_workload_1": {
        "protocol": "tests/fpga-debugging/axi-lite-s1/s1_fixed_workload_1.prot",
        "wave": "tests/fpga-debugging/axi-lite-s1/s1_fixed_workload1.vcd",
        "instances": (
            "TOP.testbench.UUT:WriteSubordinate",
            "TOP.testbench.UUT:ReadSubordinate",
        ),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "TOP.testbench.UUT.S_AXI_ACLK",
            "--show-waveform-time",
            "--time-unit",
            "ns",
            "--include-idle",
        ),
    },
    "tests.fpga-debugging.axi-stream-s2.s2_buggy": {
        "protocol": "tests/fpga-debugging/axi-stream-s2/s2_buggy.prot",
        "wave": "tests/fpga-debugging/axi-stream-s2/s2_buggy.fst",
        "instances": ("TOP.testbench.UUT.axi_stream_check:AXISManager",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.testbench.UUT.axi_stream_check.i_aclk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axi-stream-s2.s2_fixed": {
        "protocol": "tests/fpga-debugging/axi-stream-s2/s2_fixed.prot",
        "wave": "tests/fpga-debugging/axi-stream-s2/s2_fixed.fst",
        "instances": ("TOP.testbench.UUT.axi_stream_check:AXISManager",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.testbench.UUT.axi_stream_check.i_aclk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-adapter-s3.s3_buggy": {
        "protocol": "tests/fpga-debugging/axis-adapter-s3/s3_buggy.prot",
        "wave": "tests/fpga-debugging/axis-adapter-s3/s3_buggy.fst",
        "instances": ("TOP.test_axis_adapter_64_8.UUT:AXISManager",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.test_axis_adapter_64_8.UUT.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-adapter-s3.s3_fixed": {
        "protocol": "tests/fpga-debugging/axis-adapter-s3/s3_fixed.prot",
        "wave": "tests/fpga-debugging/axis-adapter-s3/s3_fixed.fst",
        "instances": ("TOP.test_axis_adapter_64_8.UUT:AXISManager",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.test_axis_adapter_64_8.UUT.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-async-fifo-c4.c4_buggy": {
        "protocol": "tests/fpga-debugging/axis-async-fifo-c4/c4_buggy.prot",
        "wave": "tests/fpga-debugging/axis-async-fifo-c4/c4_buggy.fst",
        "instances": (
            "TOP.test_axis_async_fifo.UUT.axis_reg_inst:Sender",
            "TOP.test_axis_async_fifo.UUT.axis_reg_inst:Receiver",
        ),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "TOP.test_axis_async_fifo.UUT.axis_reg_inst.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-async-fifo-c4.c4_fixed": {
        "protocol": "tests/fpga-debugging/axis-async-fifo-c4/c4_fixed.prot",
        "wave": "tests/fpga-debugging/axis-async-fifo-c4/c4_fixed.fst",
        "instances": (
            "TOP.test_axis_async_fifo.UUT.axis_reg_inst:Sender",
            "TOP.test_axis_async_fifo.UUT.axis_reg_inst:Receiver",
        ),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.test_axis_async_fifo.UUT.axis_reg_inst.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-fifo-d11.d11_buggy": {
        "protocol": "tests/fpga-debugging/axis-fifo-d11/d11_buggy.prot",
        "wave": "tests/fpga-debugging/axis-fifo-d11/d11_buggy.fst",
        "instances": ("TOP.test_axis_fifo:AxisFifo",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.test_axis_fifo.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-fifo-d11.d11_fixed": {
        "protocol": "tests/fpga-debugging/axis-fifo-d11/d11_fixed.prot",
        "wave": "tests/fpga-debugging/axis-fifo-d11/d11_fixed.fst",
        "instances": ("TOP.test_axis_fifo:AxisFifo",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.test_axis_fifo.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-fifo-d12.d12_buggy": {
        "protocol": "tests/fpga-debugging/axis-fifo-d12/d12_buggy.prot",
        "wave": "tests/fpga-debugging/axis-fifo-d12/d12_buggy.fst",
        "instances": ("TOP.test_axis_fifo:AxisFifo",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.test_axis_fifo.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-fifo-d12.d12_fixed": {
        "protocol": "tests/fpga-debugging/axis-fifo-d12/d12_fixed.prot",
        "wave": "tests/fpga-debugging/axis-fifo-d12/d12_fixed.fst",
        "instances": ("TOP.test_axis_fifo:AxisFifo",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.test_axis_fifo.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-fifo-d4.d4_buggy": {
        "protocol": "tests/fpga-debugging/axis-fifo-d4/d4_buggy.prot",
        "wave": "tests/fpga-debugging/axis-fifo-d4/d4_buggy.fst",
        "instances": ("TOP.axis_fifo_wrapper.axis_fifo_inst:AxisFifo",),
        "expect": "pass",
        "extra_args": (
            "--sample-posedge",
            "TOP.axis_fifo_wrapper.axis_fifo_inst.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.fpga-debugging.axis-fifo-d4.d4_fixed": {
        "protocol": "tests/fpga-debugging/axis-fifo-d4/d4_fixed.prot",
        "wave": "tests/fpga-debugging/axis-fifo-d4/d4_fixed.fst",
        "instances": ("TOP.axis_fifo_wrapper.axis_fifo_inst:AxisFifo",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "TOP.axis_fifo_wrapper.axis_fifo_inst.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.identities.identity_d1": {
        "protocol": "tests/identities/identity_d1.prot",
        "wave": "tests/identities/identity_d1.fst",
        "instances": ("identity_d1:Identity",),
        "expect": "pass",
    },
    "tests.multi.multi0": {
        "protocol": "tests/multi/multi0.prot",
        "wave": "tests/multi/multi0.fst",
        "instances": ("multi0:multi0",),
        "expect": "pass",
    },
    "tests.multi.multi0keep": {
        "protocol": "tests/multi/multi0keep.prot",
        "wave": "tests/multi/multi0keep.fst",
        "instances": ("multi0keep:multi0keep",),
        "expect": "pass",
    },
    "tests.multi.multi0keep2const": {
        "protocol": "tests/multi/multi0keep2const.prot",
        "wave": "tests/multi/multi0keep2const.fst",
        "instances": ("multi0keep2const:multi0keep2const",),
        "expect": "pass",
    },
    "tests.multi.multi2const": {
        "protocol": "tests/multi/multi2const.prot",
        "wave": "tests/multi/multi2const.fst",
        "instances": ("multi2const:multi2const",),
        "expect": "pass",
    },
    "tests.multi.multi2multi": {
        "protocol": "tests/multi/multi2multi.prot",
        "wave": "tests/multi/multi2multi.fst",
        "instances": ("multi2multi:multi2multi",),
        "expect": "pass",
    },
    "tests.multi.multi_data": {
        "protocol": "tests/multi/multi_data.prot",
        "wave": "tests/multi/multi_data.fst",
        "instances": ("multi_data:multi_data",),
        "expect": "pass",
    },
    "tests.multipliers.mult_d2": {
        "protocol": "tests/multipliers/mult_d2.prot",
        "wave": "tests/multipliers/mult_d2.fst",
        "instances": ("mult_d2:Multiplier",),
        "expect": "pass",
    },
    "tests.picorv32.pcpi_mul_unsigned_mul": {
        "protocol": "tests/picorv32/pcpi_mul_unsigned_mul.prot",
        "wave": "tests/picorv32/unsigned_mul.fst",
        "instances": ("picorv32_pcpi_mul:picorv32_pcpi_mul",),
        "expect": "pass",
    },
    "tests.serv.serv_regfile": {
        "protocol": "tests/serv/serv_regfile.prot",
        "wave": "tests/serv/serv_regfile.fst",
        "instances": ("serv_regfile:Regfile",),
        "expect": "pass",
        "extra_args": ("--display-hex",),
    },
    "tests.tinyaes128.aes128": {
        "protocol": "tests/tinyaes128/aes128.prot",
        "wave": "tests/tinyaes128/aes128.fst",
        "instances": ("aes_128:TinyAES128",),
        "expect": "pass",
        "extra_args": ("--display-hex",),
    },
    "tests.wal.advanced.axis": {
        "protocol": "tests/wal/advanced/axis.prot",
        "wave": "tests/wal/advanced/uart-axi.fst",
        "instances": ("uut_rx:AXIS",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "uut_rx.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.wal.advanced.axis_failing": {
        "protocol": "tests/wal/advanced/axis_failing.prot",
        "wave": "tests/wal/advanced/uart-axi-minimal.fst",
        "instances": ("uut_rx:AXIS",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "uut_rx.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.wal.advanced.axis_minimal": {
        "protocol": "tests/wal/advanced/axis_minimal.prot",
        "wave": "tests/wal/advanced/uart-axi-minimal.fst",
        "instances": ("uut_rx:AXIS",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "uut_rx.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.wal.advanced.axis_truncated": {
        "protocol": "tests/wal/advanced/axis_truncated.prot",
        "wave": "tests/wal/advanced/uart-axi-truncated.fst",
        "instances": ("uut_rx:AXIS",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "uut_rx.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ),
    },
    "tests.wal.advanced.axis_truncated_include_idle": {
        "protocol": "tests/wal/advanced/axis_truncated_include_idle.prot",
        "wave": "tests/wal/advanced/uart-axi-truncated.fst",
        "instances": ("uut_rx:AXIS",),
        "expect": None,
        "extra_args": (
            "--sample-posedge",
            "uut_rx.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
            "--include-idle",
        ),
    },
    "tests.wb_intercon.wb_arb": {
        "protocol": "tests/wb_intercon/wb_arb.prot",
        "instances": ("wb_intercon_tb.wb_arb_tb:WBSubordinate",),
        "expect": None,
        "max_steps": 1000,
        "extra_args": (
            "--sample-posedge",
            "wb_intercon_tb.wb_arb_tb.wb_clk",
            "--show-waveform-time",
            "--time-unit",
            "s",
        ),
    },
    "tests.wb_intercon.wb_cdc": {
        "protocol": "tests/wb_intercon/wb_cdc.prot",
        "wave": "tests/wb_intercon/wb_cdc.fst",
        "instances": ("wb_intercon_tb.wb_cdc_tb.dut:WBSubordinate",),
        "expect": "pass",
        "max_steps": 1000,
        "extra_args": (
            "--sample-posedge",
            "wb_intercon_tb.wb_cdc_tb.dut.wbm_clk",
            "--show-waveform-time",
            "--time-unit",
            "s",
        ),
    },
    "tests.wishbone.wishbone.bi": {
        "protocol": "tests/wishbone/wishbone.bi.prot",
        "wave": "tests/wishbone/reqwalker.vcd",
        "instances": ("TOP.reqwalker:WBSubordinate",),
        "expect": "pass",
        "extra_args": ("--sample-posedge", "TOP.reqwalker.i_clk"),
    },
}

# waveform traces from the antmicro/litex wishbone tests
ANTMICRO_TRACE_STEMS = (
    [f"fifo_classic/test_fifo_classic_{i}" for i in range(1, 9)]
    + [f"fifo_constant/test_fifo_constant_{i}" for i in range(1, 9)]
    + [
        f"sram_classic/test_sram_classic_{width}_{offset}"
        for width in (16, 1, 2, 4, 8)
        for offset in (0, 12, 4, 8)
    ]
    + [
        f"sram_incrementing/test_sram_incrementing_{width}_{offset}_{index}"
        for width in (16, 1, 2, 4, 8)
        for offset in (0, 12, 4, 8)
        for index in range(4)
    ]
)


def _antmicro_test_proto_case(stem):
    """generate a testcase for antmicro traces with the wishbone_subordinate protocol"""
    return {
        "protocol": "tests/antmicro/wishbone_subordinate.prot",
        "wave": f"tests/antmicro/{stem}.fst",
        "instances": ("tb.dut:WBSubordinate",),
        "expect": "pass",
        "extra_args": [
            "--sample-posedge",
            "tb.dut.clk",
            "--show-waveform-time",
            "--time-unit",
            "ns",
        ],
    }


BI_CASES.update(
    {
        f"tests.antmicro.{stem.replace('/', '.')}": _antmicro_test_proto_case(stem)
        for stem in ANTMICRO_TRACE_STEMS
    }
)


def _antmicro_example_proto_case(stem):
    """generate a testcase for our wishbone protocol description in examples"""
    return {
        "protocols": [
            "examples/wishbone/wishbone.prot",
            "examples/wishbone/antmicro_litex.prot",
        ],
        "wave": f"tests/antmicro/{stem}.fst",
        "instances": ("tb.dut:LitexWishbone",),
        "expect": "pass",
        "extra_args": ["--show-steps", "--display-hex"],
    }


BI_CASES.update(
    {
        f"examples.wishbone.antmicro.{stem.replace('/', '.')}": _antmicro_example_proto_case(
            stem
        )
        for stem in ANTMICRO_TRACE_STEMS
        # for now, we include only the classic (i.e. non-burst) and constant cases
        if "classic" in stem or "constant" in stem
    }
)
