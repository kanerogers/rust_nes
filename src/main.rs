use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::FromPrimitive;

#[derive(Debug, Clone)]
pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub status: u8,
    pub program_counter: u16,
    memory: [u8; 0xFFFF],
}

impl Default for CPU {
    fn default() -> Self {
        Self {
            register_a: 0,
            register_x: 0,
            status: 0,
            program_counter: 0,
            memory: unsafe { std::mem::zeroed() },
        }
    }
}

#[derive(FromPrimitive, ToPrimitive)]
pub enum Opcode {
    LDAImmediate = 0xA9,
    LDAZeroPage = 0xA5,
    LDAZeroPageX = 0xB5,
    LDAAbsolute = 0xAD,
    BRK = 0x00,
    TAX = 0xAA,
    INX = 0xE8,
    STAZeroPage = 0x85,
}

#[derive(Debug, Clone)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPageY,
    ZeroPageX,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    IndirectX,
    IndirectY,
    NoneAddressing,
}

impl CPU {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    pub fn run(&mut self) {
        loop {
            let opcode = self.mem_read(self.program_counter);
            self.program_counter += 1;

            match Opcode::from_u8(opcode) {
                Some(Opcode::LDAImmediate) => self.lda(AddressingMode::Immediate),
                Some(Opcode::LDAZeroPage) => self.lda(AddressingMode::ZeroPage),
                Some(Opcode::LDAZeroPageX) => self.lda(AddressingMode::ZeroPageX),
                Some(Opcode::LDAAbsolute) => self.lda(AddressingMode::Absolute),
                Some(Opcode::TAX) => self.tax(),
                Some(Opcode::INX) => self.inx(),
                Some(Opcode::BRK) => return,
                Some(Opcode::STAZeroPage) => self.sta(AddressingMode::ZeroPage),
                None => {
                    panic!("Unable to convert {:#02X?} into opcode", opcode);
                }
            }
        }
    }

    /// Loads a byte of memory into the accumulator setting the zero and negative flags as appropriate.
    pub fn lda(&mut self, addressing_mode: AddressingMode) {
        let addr = self.get_operand_address(&addressing_mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.check_zero_and_negative_flags(self.register_a);
        let increment = get_increment_size(&addressing_mode);
        self.program_counter += increment;
    }

    /// Transfer the value of A to X.
    pub fn tax(&mut self) {
        self.register_x = self.register_a;
        self.check_zero_and_negative_flags(self.register_x);
    }

    /// Adds one to the X register setting the zero and negative flags as appropriate.
    pub fn inx(&mut self) {
        let (x, _) = self.register_x.overflowing_add(1);
        self.register_x = x;
        self.check_zero_and_negative_flags(self.register_x);
    }

    pub fn sta(&mut self, addressing_mode: AddressingMode) {
        let addr = self.get_operand_address(&addressing_mode);
        self.mem_write(addr, self.register_a);
        let increment = get_increment_size(&addressing_mode);
        self.program_counter += increment;
    }

    pub fn check_zero_and_negative_flags(&mut self, value: u8) {
        // Check if we need to set the zero flag
        if value == 0 {
            // Set flag 1 (zero) to 1
            self.status = self.status | 0b0000_0010;
        } else {
            // Set flag 1 (zero) to 0
            self.status = self.status & 0b1111_1101;
        }

        // Check if we need to set the negative flag
        if value & 0b1000_0000 != 0 {
            // Set flag 7 (negative) to 1
            self.status = self.status | 0b1000_0000;
        } else {
            // Set flag 7 (negative) to 0
            self.status = self.status & 0b0111_1111;
        }
    }

    fn get_operand_address(&self, addressing_mode: &AddressingMode) -> u16 {
        match addressing_mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::ZeroPageX => {
                (self.mem_read(self.program_counter) + self.register_x) as u16
            }
            AddressingMode::ZeroPageY => todo!(),
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::AbsoluteX => todo!(),
            AddressingMode::AbsoluteY => todo!(),
            AddressingMode::IndirectX => todo!(),
            AddressingMode::IndirectY => todo!(),
            AddressingMode::NoneAddressing => todo!(),
        }
    }

    fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = 0;
        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }

    fn mem_read_u16(&self, addr: u16) -> u16 {
        let lo = self.mem_read(addr) as u16;
        let hi = self.mem_read(addr + 1) as u16;
        (hi << 8) | lo
    }

    fn mem_write_u16(&mut self, addr: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(addr, lo);
        self.mem_write(addr + 1, hi);
    }
}

fn get_increment_size(addressing_mode: &AddressingMode) -> u16 {
    match addressing_mode {
        AddressingMode::Absolute | AddressingMode::AbsoluteX | AddressingMode::AbsoluteY => 2,
        _ => 1,
    }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::ToPrimitive;

    #[test]
    pub fn test_lda_immediate() {
        let val = 0x05;
        let program = vec![0xA9, val, 0x00];
        let mut cpu = CPU::default();
        cpu.load_and_run(program);
        assert_eq!(cpu.register_a, val);
        assert!(cpu.status & 0b0000_0010 == 0);
        assert!(cpu.status & 0b1000_0000 == 0);
    }

    #[test]
    fn test_lda_zero_page() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x10, 0x55);
        cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

        assert_eq!(cpu.register_a, 0x55);
    }

    #[test]
    fn test_lda_zero_page_x() {
        let mut cpu = CPU::new();
        let addr = 0x02;
        let data = 0x55;
        cpu.mem_write(addr, data);
        cpu.load_and_run(vec![
            Opcode::LDAImmediate.to_u8().unwrap(),
            0x01,
            Opcode::TAX.to_u8().unwrap(),
            Opcode::LDAZeroPageX.to_u8().unwrap(),
            0x01,
            0x00,
        ]);

        assert_eq!(cpu.register_a, data);
    }

    #[test]
    fn test_lda_absolute() {
        let mut cpu = CPU::new();
        let addr = 0x0880;
        let data = 0xfa;
        cpu.mem_write(addr, data);
        cpu.load_and_run(vec![0xAD, 0x80, 0x08, 0x00]);

        assert_eq!(cpu.register_a, data);
    }

    #[test]
    pub fn test_lda_zero() {
        let val = 0x00;
        let program = vec![0xA9, val, 0x00];
        let mut cpu = CPU::default();
        cpu.load_and_run(program);
        assert_eq!(cpu.register_a, val);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    pub fn test_tax() {
        let val = 0x05;
        let program = vec![Opcode::LDAImmediate.to_u8().unwrap(), val, 0xAA, 0x00];
        let mut cpu = CPU::default();
        cpu.load_and_run(program);
        assert_eq!(cpu.register_x, val);
        assert!(cpu.status & 0b0000_0010 == 0);
        assert!(cpu.status & 0b1000_0000 == 0);
    }

    #[test]
    pub fn test_tax_zero() {
        let val = 0x00;
        let program = vec![
            0xAA,
            Opcode::LDAImmediate.to_u8().unwrap(),
            0x01,
            Opcode::LDAImmediate.to_u8().unwrap(),
            val,
            0xAA,
            0x00,
        ];
        let mut cpu = CPU::default();
        cpu.register_a = val;
        cpu.load_and_run(program);
        assert_eq!(cpu.register_x, val);
        assert_eq!(cpu.status & 0b0000_0010, 0b10);
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::default();
        cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::default();
        cpu.load_and_run(vec![
            Opcode::LDAImmediate.to_u8().unwrap(),
            0xff,
            Opcode::TAX.to_u8().unwrap(),
            0xe8,
            0xe8,
            0x00,
        ]);

        assert_eq!(cpu.register_x, 1)
    }

    #[test]
    pub fn test_sta_zero() {
        let mut cpu = CPU::default();
        let val = 0xFA;
        let addr = 124;
        cpu.load_and_run(vec![
            Opcode::LDAImmediate.to_u8().unwrap(),
            val,
            0x85,
            addr,
            0x00,
        ]);
        assert_eq!(cpu.mem_read(addr as u16), val);
    }

    #[test]
    pub fn test_sta_zero_page_x() {
        let mut cpu = CPU::default();
        let val = 0xFA;
        let addr = 124;
        cpu.load_and_run(vec![
            Opcode::LDAImmediate.to_u8().unwrap(),
            val,
            0x85,
            addr,
            0x00,
        ]);
        assert_eq!(cpu.mem_read(addr as u16), val);
    }

    #[test]
    pub fn test_u16_read_write() {
        let data = u16::MAX;
        let addr = 0x1010;
        let mut cpu = CPU::new();
        cpu.mem_write_u16(addr, data);
        assert_eq!(cpu.mem_read_u16(addr), data);
    }
}
