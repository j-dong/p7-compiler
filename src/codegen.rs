use std::io::prelude::*;
use bit_set::BitSet;

use isa;
use isa::LabelReference;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct Temporary(usize);
impl Temporary {
    fn num(&self) -> usize { let &Temporary(n) = self; n }
}
#[derive(Clone, Debug)]
struct TemporaryFactory { next: usize }
impl TemporaryFactory {
    fn new() -> TemporaryFactory {
        TemporaryFactory { next: 0 }
    }
    fn create(&mut self) -> Temporary {
        let i = self.next;
        self.next += 1;
        Temporary(i)
    }
}

#[derive(Clone, Debug)]
enum IRInstruction {
    MovReg(Temporary, Temporary),
    MovImm(Temporary, i16),
    MovLbl(Temporary, LabelReference),
    Sub(Temporary, Temporary, Temporary),
    Ld(Temporary, Temporary),
    St(Temporary, Temporary),
    // t0 = call t1
    Call(Temporary, Temporary),
    // usize are indices in Vec
    // jump instructions require a register
    Jmp(usize, Temporary),
    CondJmp(isa::JumpCondition, Temporary, usize, Temporary),
    Ret(Temporary),
}

impl IRInstruction {
    fn def_set(&self) -> BitSet {
        let mut ret: BitSet = BitSet::new();
        match self {
            &IRInstruction::MovReg(t, _) => { ret.insert(t.num()); }
            &IRInstruction::MovImm(t, _) => { ret.insert(t.num()); }
            &IRInstruction::MovLbl(t, _) => { ret.insert(t.num()); }
            &IRInstruction::Sub(t, _, _) => { ret.insert(t.num()); }
            &IRInstruction::Ld(t, _)     => { ret.insert(t.num()); }
            &IRInstruction::Call(t, _)   => { ret.insert(t.num()); }
            &IRInstruction::Jmp(_, t)    => { ret.insert(t.num()); }
            &IRInstruction::CondJmp(_, _, _, t)
                                         => { ret.insert(t.num()); }
            &IRInstruction::Ret(t)       => { ret.insert(t.num()); }
            _ => {}
        }
        ret
    }
    fn use_set(&self) -> BitSet {
        let mut ret: BitSet = BitSet::new();
        match self {
            &IRInstruction::MovReg(_, a) => { ret.insert(a.num()); }
            &IRInstruction::Sub(_, a, b) => { ret.insert(a.num()); ret.insert(b.num()); }
            &IRInstruction::Ld(_, a)     => { ret.insert(a.num()); }
            &IRInstruction::St(a, b)     => { ret.insert(a.num()); ret.insert(b.num()); }
            &IRInstruction::Call(_, a)   => { ret.insert(a.num()); }
            &IRInstruction::CondJmp(_, a, _, _)
                                         => { ret.insert(a.num()); }
            _ => {}
        }
        ret
    }
    fn succ(&self, i: usize) -> Vec<usize> {
        match self {
            &IRInstruction::Jmp(a, _) => vec![a],
            &IRInstruction::CondJmp(_, _, a, _) => vec![i + 1, a],
            &IRInstruction::Ret(_) => vec![],
            _ => vec![i + 1],
        }
    }
}

/// Computes liveness information for the given instructions.
///
/// Return value is the set of live-out variables for each instruction.
fn compute_liveness(instructions: &Vec<IRInstruction>) -> Vec<BitSet> {
    let num_inst = instructions.len();
    let mut in_set  = vec![BitSet::new(); num_inst];
    let mut out_set = vec![BitSet::new(); num_inst];
    loop {
        let mut changed = false;
        for i in (0..num_inst).rev() {
            let old_in  = in_set[i].clone();
            let old_out = out_set[i].clone();
            out_set[i].clear();
            for s in instructions[i].succ(i) {
                if s == num_inst { continue }
                out_set[i].union_with(&in_set[s]);
            }
            in_set[i] = out_set[i].clone();
            in_set[i].difference_with(&instructions[i].def_set());
            in_set[i].union_with(&instructions[i].use_set());
            if !(old_in == in_set[i] && old_out == out_set[i]) {
                changed = true;
            }
        }
        if !changed { break; }
    }
    out_set
}

pub struct CodeGenerator<'a, W: Write + 'a> {
    out: &'a W,
}

#[test]
fn test_liveness() {
    let mut fac = TemporaryFactory::new();
    let one = fac.create();
    let a = fac.create();
    let b = fac.create();
    let c = fac.create();
    let ret = fac.create();
    let label = fac.create();
    let instructions = vec![
        IRInstruction::MovImm(a, 0),
        IRInstruction::MovImm(one, 1),
        IRInstruction::Sub(b, a, one),
        IRInstruction::Sub(c, c, b),
        IRInstruction::Sub(a, b, one),
        IRInstruction::CondJmp(isa::JumpCondition::Zero, a, 2, label),
        IRInstruction::MovReg(ret, c),
    ];
    assert_eq!(compute_liveness(&instructions), vec![
        BitSet::from_bytes(&[0b01010000]), // a, c
        BitSet::from_bytes(&[0b11010000]), // one, a, c
        BitSet::from_bytes(&[0b10110000]), // one, b, c
        BitSet::from_bytes(&[0b10110000]), // one, b, c
        BitSet::from_bytes(&[0b11010000]), // one, a, c
        BitSet::from_bytes(&[0b11010000]), // one, a, c
        BitSet::from_bytes(&[0b00000000]),
    ]);
}
