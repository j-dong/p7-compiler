use std::io::prelude::*;
use bit_set::BitSet;

use isa;
use isa::{NumberedLabel, LabelReference, LabelFactory};

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
    fn count(&self) -> usize {
        self.next
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
    // pseudo-instruction
    Label(NumberedLabel),
    // usize are indices in Vec
    // jump instructions require a register
    Jmp(LabelReference, Temporary),
    CondJmp(isa::JumpCondition, Temporary, LabelReference, Temporary),
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
    fn succ(&self, i: usize, label_map: &Vec<usize>) -> Vec<usize> {
        match self {
            &IRInstruction::Jmp(LabelReference(n), _) => vec![label_map[n]],
            &IRInstruction::CondJmp(_, _, LabelReference(n), _) => vec![i + 1, label_map[n]],
            &IRInstruction::Ret(_) => vec![],
            _ => vec![i + 1],
        }
    }
}

fn resolve_labels(instructions: &Vec<IRInstruction>, num_labels: usize) -> Vec<usize> {
    let mut ret = vec![0; num_labels];
    for (i, inst) in instructions.iter().enumerate() {
        if let &IRInstruction::Label(NumberedLabel(n)) = inst {
            ret[n] = i + 1;
        }
    }
    ret
}

/// Computes liveness information for the given instructions.
///
/// Return value is the set of live-out variables for each instruction.
fn compute_liveness(instructions: &Vec<IRInstruction>, label_map: &Vec<usize>) -> Vec<BitSet> {
    let num_inst = instructions.len();
    let mut in_set  = vec![BitSet::new(); num_inst];
    let mut out_set = vec![BitSet::new(); num_inst];
    loop {
        let mut changed = false;
        for i in (0..num_inst).rev() {
            let old_in  = in_set[i].clone();
            let old_out = out_set[i].clone();
            out_set[i].clear();
            for s in instructions[i].succ(i, &label_map) {
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

#[derive(Debug, Clone)]
struct InterferenceGraph {
    edges: Vec<Vec<usize>>,
}

impl PartialEq for InterferenceGraph {
    fn eq(&self, other: &InterferenceGraph) -> bool {
        if self.edges.len() != other.edges.len() { return false; }
        for (i, neighbors) in self.edges.iter().enumerate() {
            if neighbors.len() != other.edges[i].len() { return false; }
            for neighbor in neighbors {
                if *neighbor < i { continue }
                if !other.edges[i].contains(neighbor) { return false; }
            }
        }
        true
    }
}

trait ToIndex { fn to_index(&self) -> usize; }
impl ToIndex for usize { fn to_index(&self) -> usize { *self } }
impl ToIndex for Temporary { fn to_index(&self) -> usize { let &Temporary(n) = self; n } }

impl InterferenceGraph {
    fn new(size: usize) -> InterferenceGraph {
        InterferenceGraph {
            edges: vec![vec![]; size],
        }
    }
    fn add_edge<A: ToIndex, B: ToIndex>(&mut self, node1: A, node2: B) {
        let a = node1.to_index();
        let b = node2.to_index();
        if a == b { return }
        assert!(self.edges[a].contains(&b) == self.edges[b].contains(&a));
        if self.edges[a].contains(&b) {
            return;
        }
        self.edges[a].push(b);
        self.edges[b].push(a);
    }
    fn has_edge<A: ToIndex, B: ToIndex>(&self, node1: A, node2: B) -> bool {
        let a = node1.to_index();
        let b = node2.to_index();
        self.edges[a].contains(&b)
    }
}

fn compute_interference_graph(instructions: &Vec<IRInstruction>, liveness: &Vec<BitSet>, size: usize) -> InterferenceGraph {
    let mut ret = InterferenceGraph::new(size);
    for (inst, live_out) in instructions.iter().zip(liveness.iter()) {
        if let &IRInstruction::MovReg(dest, Temporary(src)) = inst {
            for var in live_out {
                if var != src {
                    // destination doesn't interfere with source
                    ret.add_edge(dest, var);
                }
            }
        } else {
            for gen in inst.def_set().iter() {
                for var in live_out {
                    ret.add_edge(gen, var);
                }
            }
        }
    }
    ret
}

pub struct CodeGenerator<'a, W: Write + 'a> {
    out: &'a W,
}

#[test]
fn test_interference() {
    let mut fac = TemporaryFactory::new();
    let mut label_fac = LabelFactory::new();
    let loop_start = label_fac.create();
    let one = fac.create();
    let a = fac.create();
    let b = fac.create();
    let c = fac.create();
    let ret = fac.create();
    let label = fac.create();
    let instructions = vec![
        IRInstruction::MovImm(a, 0),
        IRInstruction::MovImm(one, 1),
        IRInstruction::Label(loop_start),
        IRInstruction::Sub(b, a, one),
        IRInstruction::Sub(c, c, b),
        IRInstruction::Sub(a, b, one),
        IRInstruction::CondJmp(isa::JumpCondition::Zero, a, loop_start.get_ref(), label),
        IRInstruction::MovReg(ret, c),
    ];
    let label_map = resolve_labels(&instructions, label_fac.count());
    let liveness = compute_liveness(&instructions, &label_map);
    assert_eq!(liveness, vec![
        BitSet::from_bytes(&[0b01010000]), // a, c
        BitSet::from_bytes(&[0b11010000]), // one, a, c
        BitSet::from_bytes(&[0b11010000]), // one, a, c
        BitSet::from_bytes(&[0b10110000]), // one, b, c
        BitSet::from_bytes(&[0b10110000]), // one, b, c
        BitSet::from_bytes(&[0b11010000]), // one, a, c
        BitSet::from_bytes(&[0b11010000]), // one, a, c
        BitSet::from_bytes(&[0b00000000]),
    ]);
    // def: a     live: a, c
    // def: one   live: one, a, c
    //            live: one, a, c
    // def: b     live: one, b, c
    // def: c     live: one, b, c
    // def: a     live: one, a, c
    // def: label live: one, a, c
    // def: ret (move)
    let num_vars = fac.count();
    let ig = compute_interference_graph(&instructions, &liveness, num_vars);
    let mut expected = InterferenceGraph::new(num_vars);
    expected.add_edge(a, c);
    expected.add_edge(one, a);
    expected.add_edge(one, c);
    expected.add_edge(b, c);
    expected.add_edge(b, one);
    expected.add_edge(c, one);
    expected.add_edge(label, one);
    expected.add_edge(label, a);
    expected.add_edge(label, c);
    assert_eq!(ig, expected);
}
