//! Represents the p7 ISA.

use std::fmt;
use std::fmt::Formatter;
use std::fmt::Display;

pub trait Label: Display { }

pub struct LabelReference<'a, L: Label + 'a>(&'a L);

impl<'a, L: Label> Display for LabelReference<'a, L> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let LabelReference(r) = *self;
        write!(f, "@{}", r)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct NumberedLabel(pub u64);

impl Display for NumberedLabel {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let NumberedLabel(n) = *self;
        write!(f, "label{}", n)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Register(u8);

pub const ZERO_REGISTER: Register = Register(0);

impl Register {
    pub fn new(n: u8) -> Option<Register> {
        if 1 <= n && n <= 15 {
            Some(Register(n))
        } else {
            None
        }
    }

    pub unsafe fn unchecked_new(n: u8) -> Register {
        Register(n)
    }

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
pub enum Instruction {
    Sub(Register, Register, Register),
    Mov(Register, i16),
    Jmp(Register, Register, JumpCondition),
    Ld(Register, Register),
    St(Register, Register),
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Instruction::Sub(rt, ra, rb) => write!(f, "sub {}, {}, {}", rt, ra, rb),
            Instruction::Mov(rt, imm) => write!(f, "mov {}, {}", rt, imm),
            Instruction::Jmp(rt, ra, cond) => match cond {
                JumpCondition::Zero    => write!(f, "jz {}, {}", rt, ra),
                JumpCondition::NotZero => write!(f, "jnz {}, {}", rt, ra),
                JumpCondition::Sign    => write!(f, "js {}, {}", rt, ra),
                JumpCondition::NotSign => write!(f, "jns {}, {}", rt, ra),
            },
            Instruction::Ld(rt, ra) => write!(f, "ld {}, {}", rt, ra),
            Instruction::St(rt, ra) => write!(f, "st {}, {}", rt, ra),
        }
    }
}
