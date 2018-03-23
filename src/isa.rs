//! Represents the p7 ISA.

use std::fmt;
use std::fmt::Formatter;
use std::fmt::Display;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NumberedLabel(pub u64);

impl Display for NumberedLabel {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let NumberedLabel(n) = *self;
        write!(f, "label{}", n)
    }
}

#[derive(Clone, Debug)]
pub struct LabelFactory { next: u64 }

impl LabelFactory {
    pub fn new() -> LabelFactory { LabelFactory { next: 0 } }
    pub fn create(&mut self) -> NumberedLabel {
        let i = self.next;
        self.next += 1;
        NumberedLabel(i)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LabelReference(u64);

impl Display for LabelReference {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let LabelReference(n) = *self;
        write!(f, "@label{}", n)
    }
}

impl NumberedLabel {
    pub fn get_ref(&self) -> LabelReference {
        let NumberedLabel(n) = *self;
        LabelReference(n)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Register(u8);

pub const ZERO_REGISTER: Register = Register(0);

pub const REGISTERS: [Register; 16] = [
    Register(0),  Register(1),  Register(2),  Register(3),
    Register(4),  Register(5),  Register(6),  Register(7),
    Register(8),  Register(9),  Register(10), Register(11),
    Register(12), Register(13), Register(14), Register(15),
];

impl Register {
    pub fn num(&self) -> u8 {
        let Register(n) = *self;
        n
    }
}

impl Display for Register {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let Register(n) = *self;
        write!(f, "r{}", n)
    }
}


#[derive(Copy, Clone, Debug)]
pub enum JumpCondition {
    Zero,
    NotZero,
    Sign,
    NotSign,
}

#[derive(Copy, Clone, Debug)]
pub enum Instruction<V> {
    Sub(V, V, V),
    Mov(V, i16),
    MovLabel(V, LabelReference),
    Jmp(V, V, JumpCondition),
    Ld(V, V),
    St(V, V),
}

impl<V> Display for Instruction<V> where V: Display {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            &Instruction::Sub(ref rt, ref ra, ref rb) =>
                write!(f, "sub {}, {}, {}", rt, ra, rb),
            &Instruction::Mov(ref rt, imm) =>
                write!(f, "mov {}, {}", rt, imm),
            &Instruction::MovLabel(ref rt, lbl) =>
                write!(f, "mov {}, {}", rt, lbl),
            &Instruction::Jmp(ref rt, ref ra, cond) => match cond {
                JumpCondition::Zero    => write!(f, "jz {}, {}", rt, ra),
                JumpCondition::NotZero => write!(f, "jnz {}, {}", rt, ra),
                JumpCondition::Sign    => write!(f, "js {}, {}", rt, ra),
                JumpCondition::NotSign => write!(f, "jns {}, {}", rt, ra),
            },
            &Instruction::Ld(ref rt, ref ra) =>
                write!(f, "ld {}, {}", rt, ra),
            &Instruction::St(ref rt, ref ra) =>
                write!(f, "st {}, {}", rt, ra),
        }
    }
}

pub type HWInstruction = Instruction<Register>;
