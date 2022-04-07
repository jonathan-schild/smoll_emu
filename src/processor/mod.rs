/*
 * Copyright (C) 2022 Jonathan Schild - All Rights Reserved
 */

mod decoder;
mod executor;

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
