/*
 * Copyright (C) 2022 Jonathan Schild - All Rights Reserved
 */

use crate::peripheral_devices::MMIOInterface;

use super::decoder::*;
use super::mem_util::*;
use super::Processor;

const SIGN_BIT: u8 = 7;

pub(super) fn adc(p: &mut Processor, a: AddressingModes, _opcode: u8) {
    // TEST

    let operand = match a {
        AddressingModes::Absolute => load_operand_absolute_address(p),
        AddressingModes::AbsoluteIndexedWithX => load_operand_absolute_indexed_with_x(p),
        AddressingModes::AbsoluteIndexedWithY => load_operand_absolute_indexed_with_y(p),
        AddressingModes::Immediate => load_operand_immediate(p),
        AddressingModes::ZeroPage => load_operand_zero_page(p),
        AddressingModes::ZeroPageIndexedIndirect => load_operand_zero_page_indexed_indirect(p),
        AddressingModes::ZeroPageIndexedWithX => load_operand_zero_page_indexed_with_x(p),
        AddressingModes::ZeroPageIndirect => load_operand_zero_page_indirect(p),
        AddressingModes::ZeroPageIndirectIndexedWithY => {
            load_operand_zero_page_indirect_indexed_with_y(p)
        }

        _ => return,
    };

    let carry: u8 = if p.is_carry_set() { 1 } else { 0 };

    let result_c = p.get_a().wrapping_add(carry);
    let result = result_c.wrapping_add(operand);

    let negative = is_bit_set_at(result, SIGN_BIT);

    // CHECK is this equivalent to the spec?
    let overflow_a = has_overflow_occurred(result_c, carry, p.get_a());
    let overflow_b = has_overflow_occurred(result, result_c, operand);

    let zero = result == 0;

    // CHECK is this equivalent to the spec?
    let carry_a = has_carry_occurred(result_c, carry, p.get_a());
    let carry_b = has_carry_occurred(result, result_c, operand);

    p.set_negative(negative);
    p.set_overflow(overflow_a | overflow_b);
    p.set_zero(zero);
    p.set_carry(carry_a | carry_b);

    p.set_a(result);
}

pub(super) fn and(p: &mut Processor, a: AddressingModes, _opcode: u8) {
    // TEST

    let operand = match a {
        AddressingModes::Absolute => load_operand_absolute_address(p),
        AddressingModes::AbsoluteIndexedWithX => load_operand_absolute_indexed_with_x(p),
        AddressingModes::AbsoluteIndexedWithY => load_operand_absolute_indexed_with_y(p),
        AddressingModes::Immediate => load_operand_immediate(p),
        AddressingModes::ZeroPage => load_operand_zero_page(p),
        AddressingModes::ZeroPageIndexedIndirect => load_operand_zero_page_indexed_indirect(p),
        AddressingModes::ZeroPageIndexedWithX => load_operand_zero_page_indexed_with_x(p),
        AddressingModes::ZeroPageIndirect => load_operand_zero_page_indirect(p),
        AddressingModes::ZeroPageIndirectIndexedWithY => {
            load_operand_zero_page_indirect_indexed_with_y(p)
        }
        _ => return,
    };

    let result = p.get_a() & operand;

    let negative = is_bit_set_at(result, SIGN_BIT);
    let zero = result == 0;

    p.set_negative(negative);
    p.set_zero(zero);

    p.set_a(result);
}

pub(super) fn asl(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TEST

    let operand_address;
    let operand;

    if let AddressingModes::Accumulator = a {
        operand = p.get_a();
        operand_address = 0;
    } else {
        operand_address = match a {
            AddressingModes::Absolute => load_operand_address_absolute_address(p),
            AddressingModes::AbsoluteIndexedWithX => {
                load_operand_address_absolute_indexed_with_x(p)
            }
            AddressingModes::ZeroPage => load_operand_address_zero_page(p),
            AddressingModes::ZeroPageIndexedWithX => {
                load_operand_address_zero_page_indexed_with_x(p)
            }
            _ => return,
        };

        operand = p.load(operand_address);
    }
    let result = operand << 1;

    let negative = is_bit_set_at(result, SIGN_BIT);
    let zero = result == 0;
    let carry = is_bit_set_at(operand, SIGN_BIT);

    p.set_negative(negative);
    p.set_zero(zero);
    p.set_carry(carry);

    if let AddressingModes::Accumulator = a {
        p.set_a(result);
    } else {
        p.store(operand_address, result);
    }
}

pub(super) fn bbr(p: &mut Processor, _a: AddressingModes, opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);
    let accumulator = p.get_a();

    let set = match opcode {
        0x0F => is_bit_set_at(accumulator, 0),
        0x1F => is_bit_set_at(accumulator, 1),
        0x2F => is_bit_set_at(accumulator, 2),
        0x3F => is_bit_set_at(accumulator, 3),
        0x4F => is_bit_set_at(accumulator, 4),
        0x5F => is_bit_set_at(accumulator, 5),
        0x6F => is_bit_set_at(accumulator, 6),
        0x7F => is_bit_set_at(accumulator, 7),
        _ => true,
    };

    if !set {
        p.offset_pc(offset);
    }
}

pub(super) fn bbs(p: &mut Processor, _a: AddressingModes, opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);
    let accumulator = p.get_a();

    let set = match opcode {
        0x8F => is_bit_set_at(accumulator, 0),
        0x9F => is_bit_set_at(accumulator, 1),
        0xAF => is_bit_set_at(accumulator, 2),
        0xBF => is_bit_set_at(accumulator, 3),
        0xCF => is_bit_set_at(accumulator, 4),
        0xDF => is_bit_set_at(accumulator, 5),
        0xEF => is_bit_set_at(accumulator, 6),
        0xFF => is_bit_set_at(accumulator, 7),
        _ => false,
    };

    if set {
        p.offset_pc(offset);
    }
}

pub(super) fn bcc(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);

    if !p.is_carry_set() {
        p.offset_pc(offset);
    }
}

pub(super) fn bcs(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);

    if p.is_carry_set() {
        p.offset_pc(offset);
    }
}

pub(super) fn beq(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);

    if p.is_zero_set() {
        p.offset_pc(offset);
    }
}

pub(super) fn bit(p: &mut Processor, a: AddressingModes, _opcode: u8) {
    // TEST

    let operand = match a {
        AddressingModes::Absolute => load_operand_absolute_address(p),
        AddressingModes::AbsoluteIndexedWithX => load_operand_absolute_indexed_with_x(p),
        AddressingModes::Immediate => load_operand_immediate(p),
        AddressingModes::ZeroPage => load_operand_zero_page(p),
        AddressingModes::ZeroPageIndexedWithX => load_operand_zero_page_indexed_with_x(p),
        _ => return,
    };

    p.set_negative(is_bit_set_at(operand, 7));
    p.set_overflow(is_bit_set_at(operand, 6));

    let result = p.get_a() & operand;

    p.set_zero(result == 0);
}

pub(super) fn bmi(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);

    if p.is_negative_set() {
        p.offset_pc(offset);
    }
}

pub(super) fn bne(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);

    if !p.is_zero_set() {
        p.offset_pc(offset);
    }
}

pub(super) fn bpl(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);

    if !p.is_negative_set() {
        p.offset_pc(offset);
    }
}

pub(super) fn bra(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);
    p.offset_pc(offset);
}

pub(super) fn brk(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bvc(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);

    if !p.is_overflow_set() {
        p.offset_pc(offset);
    }
}

pub(super) fn bvs(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let offset = load_operand_relative(p);

    if p.is_overflow_set() {
        p.offset_pc(offset);
    }
}

pub(super) fn clc(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    p.set_carry(false);
}

pub(super) fn cld(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    p.set_decimal(false);
}

pub(super) fn cli(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    p.set_brake(false);
}

pub(super) fn clv(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    p.set_overflow(false);
}

pub(super) fn cmp(p: &mut Processor, a: AddressingModes, _opcode: u8) {
    // TEST

    let mut operand = match a {
        AddressingModes::Absolute => load_operand_absolute_address(p),
        AddressingModes::AbsoluteIndexedWithX => load_operand_absolute_indexed_with_x(p),
        AddressingModes::AbsoluteIndexedWithY => load_operand_absolute_indexed_with_y(p),
        AddressingModes::Immediate => load_operand_immediate(p),
        AddressingModes::ZeroPage => load_operand_zero_page(p),
        AddressingModes::ZeroPageIndexedIndirect => load_operand_zero_page_indexed_indirect(p),
        AddressingModes::ZeroPageIndexedWithX => load_operand_zero_page_indexed_with_x(p),
        AddressingModes::ZeroPageIndirect => load_operand_zero_page_indirect(p),
        AddressingModes::ZeroPageIndirectIndexedWithY => {
            load_operand_zero_page_indirect_indexed_with_y(p)
        }
        _ => return,
    };

    operand = -(operand as i8) as u8;

    let result = p.get_a().wrapping_sub(operand);

    let negative = is_bit_set_at(result, SIGN_BIT);

    // CHECK is this equivalent to the spec?
    let overflow = has_overflow_occurred(result, operand, p.get_a());

    let zero = result == 0;

    // CHECK is this equivalent to the spec?
    let carry = has_carry_occurred(result, operand, p.get_a());

    p.set_negative(negative);
    p.set_overflow(overflow);
    p.set_zero(zero);
    p.set_carry(carry);
}

pub(super) fn cpx(p: &mut Processor, a: AddressingModes, _opcode: u8) {
    // TEST

    let mut operand = match a {
        AddressingModes::Absolute => load_operand_absolute_address(p),
        AddressingModes::Immediate => load_operand_immediate(p),
        AddressingModes::ZeroPage => load_operand_zero_page(p),
        _ => return,
    };

    operand = -(operand as i8) as u8;

    let result = p.get_x().wrapping_sub(operand);

    let negative = is_bit_set_at(result, SIGN_BIT);

    // CHECK is this equivalent to the spec?
    let overflow = has_overflow_occurred(result, operand, p.get_x());

    let zero = result == 0;

    // CHECK is this equivalent to the spec?
    let carry = has_carry_occurred(result, operand, p.get_x());

    p.set_negative(negative);
    p.set_overflow(overflow);
    p.set_zero(zero);
    p.set_carry(carry);
}

pub(super) fn cpy(p: &mut Processor, a: AddressingModes, _opcode: u8) {
    // TEST

    let mut operand = match a {
        AddressingModes::Absolute => load_operand_absolute_address(p),
        AddressingModes::Immediate => load_operand_immediate(p),
        AddressingModes::ZeroPage => load_operand_zero_page(p),
        _ => return,
    };

    operand = -(operand as i8) as u8;

    let result = p.get_y().wrapping_sub(operand);

    let negative = is_bit_set_at(result, SIGN_BIT);

    // CHECK is this equivalent to the spec?
    let overflow = has_overflow_occurred(result, operand, p.get_y());

    let zero = result == 0;

    // CHECK is this equivalent to the spec?
    let carry = has_carry_occurred(result, operand, p.get_y());

    p.set_negative(negative);
    p.set_overflow(overflow);
    p.set_zero(zero);
    p.set_carry(carry);
}

pub(super) fn dec(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn dex(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn dey(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn eor(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn inc(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn inx(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn iny(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn jmp(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn jsr(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn lda(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn ldx(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn ldy(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn lsr(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn nop(_p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    return;
}

pub(super) fn ora(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn pha(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn php(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn phx(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn phy(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn pla(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn plp(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn plx(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn ply(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn rmb(p: &mut Processor, _a: AddressingModes, opcode: u8) {
    // TEST

    let operand_addr = load_operand_address_zero_page(p);
    let mut operand = p.load(operand_addr);

    match opcode {
        0x07 => operand = operand & !(0x01 << 0),
        0x17 => operand = operand & !(0x01 << 1),
        0x27 => operand = operand & !(0x01 << 2),
        0x37 => operand = operand & !(0x01 << 3),
        0x47 => operand = operand & !(0x01 << 4),
        0x57 => operand = operand & !(0x01 << 5),
        0x67 => operand = operand & !(0x01 << 6),
        0x77 => operand = operand & !(0x01 << 7),
        _ => return,
    };

    p.store(operand_addr, operand);
}

pub(super) fn rol(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn ror(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn rti(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn rts(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn sbc(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn sec(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn sed(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn sei(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn smb(p: &mut Processor, _a: AddressingModes, opcode: u8) {
    // TEST

    let opernad_addr = load_operand_address_zero_page(p);
    let mut operand = p.load(opernad_addr);

    match opcode {
        0x87 => operand = operand | 0x01 << 0,
        0x97 => operand = operand | 0x01 << 1,
        0xA7 => operand = operand | 0x01 << 2,
        0xB7 => operand = operand | 0x01 << 3,
        0xC7 => operand = operand | 0x01 << 4,
        0xD7 => operand = operand | 0x01 << 5,
        0xE7 => operand = operand | 0x01 << 6,
        0xF7 => operand = operand | 0x01 << 7,
        _ => return,
    };

    p.store(opernad_addr, operand);
}

pub(super) fn sta(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn stp(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn stx(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn sty(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn stz(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn tax(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let value = p.get_a();
    p.set_negative(is_bit_set_at(value, SIGN_BIT));
    p.set_zero(value == 0);
    p.set_x(value);
}

pub(super) fn tay(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let value = p.get_a();
    p.set_negative(is_bit_set_at(value, SIGN_BIT));
    p.set_zero(value == 0);
    p.set_y(value);
}

pub(super) fn trb(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TEST

    let operand_addr = match a {
        AddressingModes::Absolute => load_operand_address_absolute_address(p),
        AddressingModes::ZeroPage => load_operand_address_zero_page(p),
        _ => return,
    };

    let mut operand = p.load(operand_addr);

    operand = !operand & p.get_a();

    p.set_zero(operand == 0);

    p.store(operand_addr, operand);
}

pub(super) fn tsb(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TEST

    let operand_addr = match a {
        AddressingModes::Absolute => load_operand_address_absolute_address(p),
        AddressingModes::ZeroPage => load_operand_address_zero_page(p),
        _ => return,
    };

    let mut operand = p.load(operand_addr);

    operand = operand | p.get_a();

    p.set_zero(operand == 0);

    p.store(operand_addr, operand);
}

pub(super) fn tsx(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let value = p.get_stack();
    p.set_negative(is_bit_set_at(value, SIGN_BIT));
    p.set_zero(value == 0);
    p.set_x(value);
}

pub(super) fn txa(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let value = p.get_x();
    p.set_negative(is_bit_set_at(value, SIGN_BIT));
    p.set_zero(value == 0);
    p.set_a(value);
}

pub(super) fn txs(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let value = p.get_x();
    p.set_stack(value);
}

pub(super) fn tya(p: &mut Processor, _a: AddressingModes, _opcode: u8) {
    // TEST

    let value = p.get_y();
    p.set_negative(is_bit_set_at(value, SIGN_BIT));
    p.set_zero(value == 0);
    p.set_a(value);
}

pub(super) fn wai(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn unknown(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

/// Returns `true` if `bit` is set at position `pos`.
///
/// If `pos` is greater than 7, `false` is returned.
///
/// # Arguments
///
/// * `value: u8` - Value to test `bit`.
/// * `pos: u8` - Position to test.
///
/// # Returns
///
/// * `bool` - `true` if bit at `pos` is set.
///
fn is_bit_set_at(value: u8, pos: u8) -> bool {
    if pos > SIGN_BIT {
        false
    } else {
        value >> pos & 0x01 != 0
    }
}

/// Returns `true` if the operand signs are equal and the `result` is different than the operand signs.
///
/// # Arguments
///
/// * `result: u8` - Result of a two's complement operation.
/// * `operand_a: u8` - Operand of a two's complement operation.
/// * `operand_b: u8` - Operand of a two's complement operation.
///
/// # Returns
///
/// * `bool` - `true` if a two's complement overflow occurred.
///
fn has_overflow_occurred(result: u8, operand_a: u8, operand_b: u8) -> bool {
    // TEST

    let a = is_bit_set_at(operand_a, SIGN_BIT);
    let b = is_bit_set_at(operand_b, SIGN_BIT);
    let r = is_bit_set_at(result, SIGN_BIT);

    // is true if sign bits of a or b are equal and the sign bits of a, b or r are not equal
    (a & b | !a & !b) & !(r & a | !r & !a)
}

/// Returns `true` if a carry occurred.
///
/// # Arguments
///
/// * `result: u8` - Result of an operation.
/// * `operand_a: u8` - Operand of an operation.
/// * `operand_b: u8` - Operand of an operation.
///
/// # Returns
///
/// * `bool` - `true` if a carry occurred.
///
fn has_carry_occurred(result: u8, operand_a: u8, operand_b: u8) -> bool {
    (result < operand_a) | (result < operand_b)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_is_bit_set_at_true() {
        assert_eq!(true, is_bit_set_at(0xFF, 0));
        assert_eq!(true, is_bit_set_at(0xFF, 7));
        assert_eq!(true, is_bit_set_at(0xFF, 3));

        assert_eq!(true, is_bit_set_at(0b01011010, 1));
        assert_eq!(true, is_bit_set_at(0b01011010, 3));
        assert_eq!(true, is_bit_set_at(0b01011010, 4));
        assert_eq!(true, is_bit_set_at(0b01011010, 6));
    }

    #[test]
    fn test_is_bit_set_at_false() {
        assert_eq!(false, is_bit_set_at(0x00, 0));
        assert_eq!(false, is_bit_set_at(0x00, 7));
        assert_eq!(false, is_bit_set_at(0x00, 3));

        assert_eq!(false, is_bit_set_at(0b01011010, 0));
        assert_eq!(false, is_bit_set_at(0b01011010, 2));
        assert_eq!(false, is_bit_set_at(0b01011010, 5));
        assert_eq!(false, is_bit_set_at(0b01011010, 7));

        assert_eq!(false, is_bit_set_at(0xFF, 8));
        assert_eq!(false, is_bit_set_at(0xFF, 0xFF));
    }

    #[test]
    fn test_has_carry_occurred() {
        let a: u8 = 0xFF;
        let b: u8 = 0x01;
        let c: u8 = 0xFE;
        let d: u8 = 0x00;
        let e: u8 = 0x02;
        let f: u8 = 0x03;

        assert_eq!(true, has_carry_occurred(d, a, b));
        assert_eq!(true, has_carry_occurred(c, a, a));

        assert_eq!(false, has_carry_occurred(e, b, b));
        assert_eq!(false, has_carry_occurred(f, e, b));
    }
}
