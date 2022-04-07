/*
 * Copyright (C) 2022 Jonathan Schild - All Rights Reserved
 */

pub trait MMIOInterface {
    fn load(&mut self, address: u16) -> u8;
    fn store(&mut self, address: u16, data: u8);
}
