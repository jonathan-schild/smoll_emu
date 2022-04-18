/*
 * Copyright (C) 2022 Jonathan Schild - All Rights Reserved
 */

use super::MMIOInterface;
use super::Processor;

pub(super) fn load_operand_address_absolute_address(p: &mut Processor) -> u16 {
    // TEST

    let pc = p.get_pc();
    p.offset_pc(2);
    let addr = (p.load(pc.wrapping_add(1)), p.load(pc));
    concatenate_address(addr)
}

pub(super) fn load_operand_address_absolute_indexed_with_x(p: &mut Processor) -> u16 {
    // TEST

    let pc = p.get_pc();
    p.offset_pc(2);
    let addr = (p.load(pc.wrapping_add(1)), p.load(pc));
    concatenate_address(addr).wrapping_add(p.get_x() as u16)
}

pub(super) fn load_operand_address_absolute_indexed_with_y(p: &mut Processor) -> u16 {
    // TEST

    let pc = p.get_pc();
    p.offset_pc(2);
    let addr = (p.load(pc.wrapping_add(1)), p.load(pc));
    concatenate_address(addr).wrapping_add(p.get_y() as u16)
}

pub(super) fn load_operand_address_zero_page(p: &mut Processor) -> u16 {
    // TEST

    let addr = p.load(p.get_pc());
    p.increment_pc();
    concatenate_address((0, addr))
}

pub(super) fn load_operand_address_zero_page_indexed_indirect(p: &mut Processor) -> u16 {
    // TEST

    let mut addr = p.load(p.get_pc());
    p.increment_pc();
    addr = addr.wrapping_add(p.get_x());
    let mut addr_indirect = concatenate_address((0, addr));
    concatenate_address((p.load(addr_indirect.wrapping_add(1)), p.load(addr_indirect)))
}

pub(super) fn load_operand_address_zero_page_indexed_with_x(p: &mut Processor) -> u16 {
    // TEST

    let addr = p.load(p.get_pc());
    p.increment_pc();
    concatenate_address((0, addr.wrapping_add(p.get_x())))
}

pub(super) fn load_operand_address_zero_page_indexed_with_y(p: &mut Processor) -> u16 {
    // TEST

    let addr = p.load(p.get_pc());
    p.increment_pc();
    concatenate_address((0, addr.wrapping_add(p.get_y())))
}

pub(super) fn load_operand_address_zero_page_indirect(p: &mut Processor) -> u16 {
    // TEST

    let addr = p.load(p.get_pc());
    p.increment_pc();
    let addr_indirect = concatenate_address((0, addr));
    concatenate_address((p.load(addr_indirect.wrapping_add(1)), p.load(addr_indirect)))
}

pub(super) fn load_operand_address_zero_page_indirect_indexed_with_y(p: &mut Processor) -> u16 {
    // TEST

    let mut addr = concatenate_address((0, p.load(p.get_pc())));
    addr.wrapping_add(p.get_y() as u16)
}

pub(super) fn load_operand_absolute_address(p: &mut Processor) -> u8 {
    // TODO

    0
}

pub(super) fn load_operand_absolute_indexed_with_x(p: &mut Processor) -> u8 {
    // TODO

    0
}

pub(super) fn load_operand_absolute_indexed_with_y(p: &mut Processor) -> u8 {
    // TODO

    0
}

pub(super) fn load_operand_immediate(p: &mut Processor) -> u8 {
    // TEST

    let operand = p.load(p.get_pc());
    p.increment_pc();
    operand
}

pub(super) fn load_operand_relative(p: &mut Processor) -> u8 {
    // TEST

    let pc = p.get_pc();
    p.offset_pc(1);
    p.load(pc)
}

pub(super) fn load_operand_zero_page(p: &mut Processor) -> u8 {
    // TODO

    0
}

pub(super) fn load_operand_zero_page_indexed_indirect(p: &mut Processor) -> u8 {
    // TODO

    0
}

pub(super) fn load_operand_zero_page_indexed_with_x(p: &mut Processor) -> u8 {
    // TODO

    0
}

pub(super) fn load_operand_zero_page_indexed_with_y(p: &mut Processor) -> u8 {
    // TODO

    0
}

pub(super) fn load_operand_zero_page_indirect(p: &mut Processor) -> u8 {
    // TODO
    0
}

pub(super) fn load_operand_zero_page_indirect_indexed_with_y(p: &mut Processor) -> u8 {
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
pub(super) fn concatenate_address(addr: (u8, u8)) -> u16 {
    let (high, low) = addr;
    (high as u16) << 8 | low as u16
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
}
