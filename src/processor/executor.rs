/*
 * Copyright (C) 2022 Jonathan Schild - All Rights Reserved
 */

use super::decoder::*;
use super::MMIOInterface;
use super::Processor;

const sign_bit: u8 = 7;

pub(super) fn adc(p: &mut Processor, a: AddressingModes, _opcode: u8) {
    // TEST

    let operand = match a {
        AddressingModes::Absolute => absolute_address(p),
        AddressingModes::AbsoluteIndexedWithX => absolute_indexed_with_x(p),
        AddressingModes::AbsoluteIndexedWithY => absolute_indexed_with_y(p),
        AddressingModes::Immediate => immediate(p),
        AddressingModes::ZeroPage => zero_page(p),
        AddressingModes::ZeroPageIndexedIndirect => zero_page_indexed_indirect(p),
        AddressingModes::ZeroPageIndexedWithX => zero_page_indexed_with_x(p),
        AddressingModes::ZeroPageIndirect => zero_page_indirect(p),
        AddressingModes::ZeroPageIndirectIndexedWithY => zero_page_indirect_indexed_with_y(p),
        _ => return,
    };

    let carry: u8 = if p.is_carry_set() { 1 } else { 0 };

    let result_c = p.get_a().wrapping_add(carry);
    let result = result_c.wrapping_add(operand);

    let negative = is_bit_set_at(result, sign_bit);

    // CHECK is this equivalent to the spec?
    let overflow_a = is_overflow(result_c, carry, p.get_a());
    let overflow_b = is_overflow(result, result_c, operand);

    let zero = result == 0;

    // CHECK is this equivalent to the spec?
    let carry_a = is_carry(result_c, carry, p.get_a());
    let carry_b = is_carry(result, result_c, operand);

    p.set_negative(negative);
    p.set_overflow(overflow_a | overflow_b);
    p.set_zero(zero);
    p.set_carry(carry_a | carry_b);
}

pub(super) fn and(p: &mut Processor, a: AddressingModes, _opcode: u8) {
    // TEST

    let operand = match a {
        AddressingModes::Absolute => absolute_address(p),
        AddressingModes::AbsoluteIndexedWithX => absolute_indexed_with_x(p),
        AddressingModes::AbsoluteIndexedWithY => absolute_indexed_with_y(p),
        AddressingModes::Immediate => immediate(p),
        AddressingModes::ZeroPage => zero_page(p),
        AddressingModes::ZeroPageIndexedIndirect => zero_page_indexed_indirect(p),
        AddressingModes::ZeroPageIndexedWithX => zero_page_indexed_with_x(p),
        AddressingModes::ZeroPageIndirect => zero_page_indirect(p),
        AddressingModes::ZeroPageIndirectIndexedWithY => zero_page_indirect_indexed_with_y(p),
        _ => return,
    };

    let result = p.get_a() & operand;

    let negative = is_bit_set_at(result, sign_bit);
    let zero = result == 0;

    p.set_negative(negative);
    p.set_zero(zero);
}

pub(super) fn asl(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TEST

    let operand = match a {
        AddressingModes::Absolute => absolute_address(p),
        AddressingModes::AbsoluteIndexedWithX => absolute_indexed_with_x(p),
        AddressingModes::Accumulator => p.get_a(),
        AddressingModes::ZeroPage => zero_page(p),
        AddressingModes::ZeroPageIndexedWithX => zero_page_indexed_with_x(p),
        _ => return,
    };

    let result = operand << 1;

    let negative = is_bit_set_at(result, sign_bit);
    let zero = result == 0;
    let carry = is_bit_set_at(operand, sign_bit);

    p.set_negative(negative);
    p.set_zero(zero);
    p.set_carry(carry);

    p.set_a(result);
}

pub(super) fn bbr(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bbs(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bcc(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bcs(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn beq(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bit(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bmi(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bne(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bpl(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bra(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn brk(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bvc(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn bvs(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn clc(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn cld(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn cli(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn clv(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn cmp(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn cpx(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn cpy(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
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

pub(super) fn nop(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
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

pub(super) fn rmb(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
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

pub(super) fn smb(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
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

pub(super) fn tax(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn tay(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn trb(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn tsb(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn tsx(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn txa(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn txs(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn tya(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn wai(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

pub(super) fn unknown(p: &mut Processor, a: AddressingModes, opcode: u8) {
    // TODO
}

fn absolute_address(p: &mut Processor) -> u8 {
    // TEST

    let pc = p.get_pc();
    p.offset_pc(2);
    let addr = (p.load(pc + 1), p.load(pc));
    p.load(concatenate_address(addr))
}

fn absolute_indexed_with_x(p: &mut Processor) -> u8 {
    // TEST

    let pc = p.get_pc();
    p.offset_pc(2);
    let addr = (p.load(pc + 1), p.load(pc));
    p.load(concatenate_address(addr).wrapping_add(p.get_x() as u16))
}

fn absolute_indexed_with_y(p: &mut Processor) -> u8 {
    // TEST

    let pc = p.get_pc();
    p.offset_pc(2);
    let addr = (p.load(pc + 1), p.load(pc));
    p.load(concatenate_address(addr).wrapping_add(p.get_y() as u16))
}

fn immediate(p: &mut Processor) -> u8 {
    // TEST

    let operand = p.load(p.get_pc());
    p.increment_pc();
    operand
}

fn zero_page(p: &mut Processor) -> u8 {
    // TEST

    let addr = p.load(p.get_pc());
    p.increment_pc();
    p.load(concatenate_address((0, addr)))
}

fn zero_page_indexed_indirect(p: &mut Processor) -> u8 {
    // TEST

    let addr = p.load(p.get_pc());
    p.increment_pc();
    // TODO
    0
}

fn zero_page_indexed_with_x(p: &mut Processor) -> u8 {
    // TEST

    let addr = p.load(p.get_pc());
    p.increment_pc();
    p.load(concatenate_address((0, addr.wrapping_add(p.get_x()))))
}

fn zero_page_indexed_with_y(p: &mut Processor) -> u8 {
    // TEST

    let addr = p.load(p.get_pc());
    p.increment_pc();
    p.load(concatenate_address((0, addr.wrapping_add(p.get_y()))))
}

fn zero_page_indirect(p: &mut Processor) -> u8 {
    // TODO
    0
}

fn zero_page_indirect_indexed_with_y(p: &mut Processor) -> u8 {
    // TODO
    0
}

/// Concatenates two bytes to a 16 bit address.
///
/// # Arguments
///
/// * `addr: (u8, u8)` - Tuple containing (high byte, low byte).
///
/// # Returns
///
/// * `u16` - 16 bit address.
///
fn concatenate_address(addr: (u8, u8)) -> u16 {
    let (high, low) = addr;
    (high as u16) << 8 | low as u16
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
    if pos > sign_bit {
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
fn is_overflow(result: u8, operand_a: u8, operand_b: u8) -> bool {
    // TEST

    let a = is_bit_set_at(operand_a, sign_bit);
    let b = is_bit_set_at(operand_b, sign_bit);
    let r = is_bit_set_at(result, sign_bit);

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
fn is_carry(result: u8, operand_a: u8, operand_b: u8) -> bool {
    (result < operand_a) | (result < operand_b)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_concatenate_address() {
        assert_eq!(0xFFFF, concatenate_address((0xFF, 0xFF)));
        assert_eq!(0xFF00, concatenate_address((0xFF, 0x00)));
        assert_eq!(0x00FF, concatenate_address((0x00, 0xFF)));
        assert_eq!(0x01FF, concatenate_address((0x01, 0xFF)));
        assert_eq!(0xFF01, concatenate_address((0xFF, 0x01)));
        assert_eq!(0x1234, concatenate_address((0x12, 0x34)));
    }

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
    fn test_is_carry() {
        let a: u8 = 0xFF;
        let b: u8 = 0x01;
        let c: u8 = 0xFE;
        let d: u8 = 0x00;
        let e: u8 = 0x02;
        let f: u8 = 0x03;

        assert_eq!(true, is_carry(d, a, b));
        assert_eq!(true, is_carry(c, a, a));

        assert_eq!(false, is_carry(e, b, b));
        assert_eq!(false, is_carry(f, e, b));
    }
}
