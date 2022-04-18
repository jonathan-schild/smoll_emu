/*
 * Copyright (C) 2022 Jonathan Schild - All Rights Reserved
 */

mod decoder;
mod executor;
mod mem_util;

use std::cell::RefCell;
use std::rc::Rc;

use super::peripheral_devices::MMIOInterface;

struct Processor {
    accumulator: u8,
    index_y: u8,
    index_x: u8,
    pc: u16,
    stack: u8,
    status: u8,
    bus: Rc<RefCell<dyn MMIOInterface>>,
}

impl MMIOInterface for Processor {
    fn load(&mut self, address: u16) -> u8 {
        // TODO
        0
    }
    fn store(&mut self, address: u16, data: u8) {
        // TODO
    }
}

impl Processor {
    fn set_a(&mut self, accumulator: u8) {
        self.accumulator = accumulator;
    }

    fn get_a(&self) -> u8 {
        self.accumulator
    }

    fn set_y(&mut self, index_y: u8) {
        self.index_y = index_y;
    }

    fn get_y(&self) -> u8 {
        self.index_y
    }

    fn set_x(&mut self, index_x: u8) {
        self.index_x = index_x;
    }

    fn get_x(&self) -> u8 {
        self.index_x
    }

    fn set_pc(&mut self, pc: u16) {
        self.pc = pc;
    }

    fn increment_pc(&mut self) {
        // TODO
    }

    fn offset_pc(&mut self, offset: u8) {
        // TODO
    }

    fn get_pc(&self) -> u16 {
        self.pc
    }

    fn set_stack(&mut self, stack: u8) {
        // TODO
        self.stack = stack;
    }

    fn get_stack(&self) -> u8 {
        // TODO
        self.stack
    }

    fn is_negative_set(&self) -> bool {
        // TODO
        false
    }

    fn is_overflow_set(&self) -> bool {
        // TODO
        false
    }

    fn is_user_defined_set(&self) -> bool {
        true
    }

    fn is_break_set(&self) -> bool {
        // TODO
        false
    }

    fn is_decimal_set(&self) -> bool {
        false
    }

    fn is_zero_set(&self) -> bool {
        // TODO
        false
    }
    fn is_carry_set(&self) -> bool {
        // TODO
        false
    }

    fn set_negative(&mut self, flag: bool) {
        // TODO
    }

    fn set_overflow(&mut self, flag: bool) {
        // TODO
    }

    fn set_user_defined(&mut self, flag: bool) {
        // TODO
    }

    fn set_brake(&mut self, flag: bool) {
        // TODO
    }

    fn set_decimal(&mut self, flag: bool) {
        // TODO
    }

    fn set_zero(&mut self, flag: bool) {
        // TODO
    }
    fn set_carry(&mut self, flag: bool) {
        // TODO
    }
}
