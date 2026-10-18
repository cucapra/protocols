use patronus::expr::{Context, ExprRef, TypeCheck};

/// Add an offset to a valid bank index, wrapping at `modulus`.
pub fn mod_add(ctx: &mut Context, value: ExprRef, amount: usize, modulus: usize) -> ExprRef {
    assert!(modulus > 0);
    if amount.is_multiple_of(modulus) {
        return value;
    }
    let width = value.get_bv_type(ctx).unwrap();
    let amount = amount % modulus;
    let amount_expr = ctx.bit_vec_val(amount, width);
    let threshold = ctx.bit_vec_val(modulus - amount, width);
    let wrapped = ctx.sub(value, threshold);
    let normal = ctx.add(value, amount_expr);
    let overflow = ctx.greater_or_equal(value, threshold);
    ctx.ite(overflow, wrapped, normal)
}

/// Read logical FIFO slot `slot` from physical banks relative to `head`.
pub fn read_bank(ctx: &mut Context, head: ExprRef, slot: usize, banks: &[ExprRef]) -> ExprRef {
    assert!(!banks.is_empty());
    let mut read = ctx.zero(banks[0].get_bv_type(ctx).unwrap());
    let width = head.get_bv_type(ctx).unwrap();
    for head_value in 0..banks.len() {
        let index = ctx.bit_vec_val(head_value, width);
        let at_head = ctx.equal(head, index);
        read = ctx.ite(at_head, banks[(head_value + slot) % banks.len()], read);
    }
    read
}
