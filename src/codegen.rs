use std::io::prelude::*;
use std::cmp;
use std::ops;
use std::vec;
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
    MovReg { dest: Temporary, src: Temporary },
    MovImm { dest: Temporary, imm: i16 },
    MovLbl { dest: Temporary, lbl: LabelReference },
    Sub { dest: Temporary, a: Temporary, b: Temporary },
    Ld { dest: Temporary, addr: Temporary },
    St { src:  Temporary, addr: Temporary },
    Alloca { bytes: usize },
    LdStack { dest: Temporary, offset: usize },
    // t0 = call t1(...)
    Call { dest: Temporary, addr: Temporary, args: Vec<Temporary> },
    // pseudo-instruction
    Label(NumberedLabel),
    // jump instructions require a register
    Jmp { target: LabelReference, addr: Temporary },
    CondJmp { cond: isa::JumpCondition, reg: Temporary, target: LabelReference, addr: Temporary },
    Ret { addr: Temporary, value: Option<Temporary> },
}

impl IRInstruction {
    fn is_jump(&self) -> bool {
        match self {
            &IRInstruction::Jmp{..} => true,
            &IRInstruction::CondJmp{..} => true,
            &IRInstruction::Ret{..} => true,
            _ => false
        }
    }
    fn is_label(&self) -> bool {
        match self {
            &IRInstruction::Label{..} => true,
            _ => false
        }
    }
    fn def_set(&self) -> BitSet {
        let mut ret: BitSet = BitSet::new();
        match self {
            &IRInstruction::MovReg { dest, .. }  => { ret.insert(dest.num()); }
            &IRInstruction::MovImm { dest, .. }  => { ret.insert(dest.num()); }
            &IRInstruction::MovLbl { dest, .. }  => { ret.insert(dest.num()); }
            &IRInstruction::Sub { dest, .. }     => { ret.insert(dest.num()); }
            &IRInstruction::Ld { dest, .. }      => { ret.insert(dest.num()); }
            &IRInstruction::LdStack { dest, .. } => { ret.insert(dest.num()); }
            &IRInstruction::Call { dest, .. }    => { ret.insert(dest.num()); }
            &IRInstruction::Jmp { addr, .. }     => { ret.insert(addr.num()); }
            &IRInstruction::CondJmp { addr, .. } => { ret.insert(addr.num()); }
            &IRInstruction::Ret { addr, .. }     => { ret.insert(addr.num()); }
            _ => {}
        }
        ret
    }
    fn use_set(&self) -> BitSet {
        let mut ret: BitSet = BitSet::new();
        match self {
            &IRInstruction::MovReg { src, .. } => { ret.insert(src.num()); }
            &IRInstruction::Sub { a, b, .. } => { ret.insert(a.num()); ret.insert(b.num()); }
            &IRInstruction::Ld { addr, .. } => { ret.insert(addr.num()); }
            &IRInstruction::St { src, addr } => { ret.insert(src.num()); ret.insert(addr.num()); }
            &IRInstruction::Call { addr, ref args, .. } => {
                ret.insert(addr.num());
                for arg in args {
                    ret.insert(arg.num());
                }
            }
            &IRInstruction::CondJmp { reg, .. } => { ret.insert(reg.num()); }
            &IRInstruction::Ret { value: Some(val), .. } => { ret.insert(val.num()); }
            _ => {}
        }
        ret
    }
    fn def_interfere(&self) -> Vec<Temporary> {
        // used variables that cannot be assigned the same register
        // as a defined variable
        match self {
            &IRInstruction::CondJmp { reg, .. } => vec![reg],
            &IRInstruction::Ret { value: Some(value), .. } => vec![value],
            _ => vec![]
        }
    }
    fn succ(&self, i: usize, label_map: &Vec<usize>) -> Vec<usize> {
        match self {
            &IRInstruction::Jmp { target: LabelReference(n), .. } => vec![label_map[n]],
            &IRInstruction::CondJmp {target: LabelReference(n), .. } => vec![i + 1, label_map[n]],
            &IRInstruction::Ret { .. } => vec![],
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
    fn size(&self) -> usize {
        self.edges.len()
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
    fn remove_edges<A: ToIndex>(&mut self, node1: A) {
        let a = node1.to_index();
        let neighbors = self.edges[a].clone();
        for b in neighbors.into_iter() {
            let ia = self.edges[b].iter().position(|&x| x == a).unwrap();
            self.edges[b].swap_remove(ia);
        }
        self.edges[a].clear();
    }
    fn degree<A: ToIndex>(&self, node: A) -> usize {
        self.edges[node.to_index()].len()
    }
}

fn compute_interference_graph(instructions: &Vec<IRInstruction>, liveness: &Vec<BitSet>, size: usize) -> InterferenceGraph {
    let mut ret = InterferenceGraph::new(size);
    for (inst, live_out) in instructions.iter().zip(liveness.iter()) {
        if let &IRInstruction::MovReg { dest, src: Temporary(src) } = inst {
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
                for var in inst.def_interfere().into_iter() {
                    ret.add_edge(gen, var);
                }
            }
        }
    }
    ret
}

#[derive(Debug, PartialEq, PartialOrd, Copy, Clone)]
struct ValidFloat(f32);
impl ValidFloat {
    fn checked(f: f32) -> ValidFloat {
        assert!(!f.is_nan());
        ValidFloat(f)
    }
}
impl Ord for ValidFloat {
    fn cmp(&self, other: &ValidFloat) -> cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}
impl Eq for ValidFloat {}

#[derive(Debug, Clone, PartialEq, Eq)]
struct VariableMap<T>(Vec<T>);

impl<T: Clone + Default> VariableMap<T> {
    fn new(size: usize) -> VariableMap<T> {
        VariableMap(vec![Default::default(); size])
    }
}

impl<I: ToIndex, T> ops::Index<I> for VariableMap<T> {
    type Output = T;
    fn index(&self, index: I) -> &T {
        &self.0[index.to_index()]
    }
}

impl<I: ToIndex, T> ops::IndexMut<I> for VariableMap<T> {
    fn index_mut(&mut self, index: I) -> &mut T {
        &mut self.0[index.to_index()]
    }
}

impl<T> IntoIterator for VariableMap<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;
    fn into_iter(self) -> vec::IntoIter<T> {
        self.0.into_iter()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Color(usize);

/// Computes an approximate graph coloring for the given graph.
/// Algorithm used is by Preston Briggs
/// [Register Allocation via Graph Coloring (1992)].
///
/// Return value is `Ok(colors)` or `Err(spill)`,
/// where `colors` is a map from node to color
/// and `spill` is a list of spilled nodes.
fn compute_graph_coloring(graph: &InterferenceGraph, ncolors: usize, spill_costs: &Vec<f32>) -> Result<VariableMap<Color>, Vec<Temporary>> {
    assert_eq!(graph.size(), spill_costs.len());
    let mut mod_graph = graph.clone();
    let mut nodes: Vec<_> = (0..graph.size()).collect();
    let mut stack = vec![];
    loop {
        // until all nodes are on stack
        loop {
            let node_count = nodes.len();
            let mut i = 0;
            let mut done = true;
            for _ in 0..node_count {
                let node = nodes[i];
                // remove nodes with fewer than k neighbors
                if mod_graph.degree(node) < ncolors {
                    mod_graph.remove_edges(node);
                    nodes.swap_remove(i);
                    stack.push(node);
                    done = false;
                } else {
                    i += 1;
                }
            }
            if done { break }
        }
        if nodes.len() == 0 { break }
        // pick node heuristically
        let (spill_index, &spill_node) = nodes.iter().enumerate().min_by_key(|&(_, &n)| ValidFloat::checked(spill_costs[n] / (mod_graph.degree(n) as f32))).unwrap();
        nodes.swap_remove(spill_index);
        mod_graph.remove_edges(spill_node);
        stack.push(spill_node);
    }
    let mut colors: VariableMap<Option<Color>> = VariableMap::new(graph.size());
    let mut available_colors = vec![true; ncolors];
    let mut to_spill = vec![];
    while let Some(node) = stack.pop() {
        assert!(colors[node].is_none());
        for i in 0..ncolors { available_colors[i] = true; }
        for &neighbor in &graph.edges[node] {
            if let Some(Color(color)) = colors[neighbor] {
                available_colors[color] = false;
            }
        }
        let color = available_colors.iter().position(|&x| x);
        if let Some(c) = color {
            colors[node] = Some(Color(c));
        } else {
            to_spill.push(Temporary(node));
        }
    }
    if to_spill.len() > 0 {
        Err(to_spill)
    } else {
        Ok(VariableMap(colors.into_iter().collect::<Option<Vec<Color>>>().unwrap()))
    }
}

fn compute_spill_costs(instructions: &Vec<IRInstruction>, num_vars: usize) -> Vec<f32> {
    let mut costs = vec![];
    // TODO
    costs
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BasicBlock {
    /// Range of instruction indices.
    range: ops::Range<usize>,
    /// List of successor indices (at most 2). Sorted.
    succ: Vec<usize>,
    /// Whether or not a block is reachable (`true` initially).
    reachable: bool,
    /// List of predecessor indices.
    pred: Vec<usize>,
    /// Immediate dominator (0 initially).
    idom: usize,
    /// Loop depth (0 initially).
    depth: usize,
}

/// Contains a number of basic blocks in sorted order.
/// The first block is the entry point of the function.
/// Labels are not included in any basic block.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ControlFlowGraph {
    blocks: Vec<BasicBlock>,
}

impl ControlFlowGraph {
    fn start(&self) -> &BasicBlock { &self.blocks[0] }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Loop {
    header: usize,
    body: Vec<usize>,
}

fn construct_cfg(instructions: &Vec<IRInstruction>, num_labels: usize) -> ControlFlowGraph {
    let mut ret = ControlFlowGraph { blocks: vec![] };
    // construct blocks while resolving labels
    let mut i = 0;
    let mut label_map = vec![0; num_labels];
    'segment:
    while i < instructions.len() {
        while let &IRInstruction::Label(NumberedLabel(n)) = &instructions[i] {
            label_map[n] = ret.blocks.len();
            i += 1;
            if i >= instructions.len() { break 'segment; }
        }
        let range_start = i;
        let range_end = loop {
            if instructions[i].is_label() { break i; }
            if instructions[i].is_jump() { i += 1; break i; }
            i += 1;
            if i >= instructions.len() { break i; }
        };
        ret.blocks.push(BasicBlock {
            range: range_start..range_end,
            succ: vec![],
            reachable: true,
            pred: vec![],
            idom: 0,
            depth: 0,
        });
    }
    // resolve successors
    let num_blocks = ret.blocks.len();
    for i in 0..num_blocks {
        {
            let block = &mut ret.blocks[i];
            block.succ = instructions[block.range.end - 1].succ(i, &label_map);
            // also remove successors that don't exist
            block.succ.retain(|&i| i < num_blocks);
            block.succ.sort();
        }
        let succ = ret.blocks[i].succ.clone();
        for j in succ.into_iter() {
            ret.blocks[j].pred.push(i);
        }
    }
    ret
}

impl ControlFlowGraph {
    fn postorder(&self, start: usize, order: &mut Vec<usize>, visited: &mut Vec<bool>) {
        assert!(!visited[start]);
        visited[start] = true;
        for &succ in &self.blocks[start].succ {
            if !visited[succ] {
                self.postorder(succ, order, visited);
            }
        }
        order.push(start);
    }

    /// Computes immediate dominators for each block,
    /// forming a dominator tree.
    /// Also sets reachable.
    /// Algorithm used is by Cooper, Harvey, and Kennedy
    /// [A Simple, Fast Dominance Algorithm (2001)].
    fn compute_dominators(&mut self) {
        // compute RPO (except first)
        let rpo = {
            let mut order = vec![];
            let mut visited = vec![false; self.blocks.len()];
            self.postorder(0, &mut order, &mut visited);
            let popped = order.pop();
            assert!(popped == Some(0));
            order.reverse();
            order
        };
        const UNDEFINED: usize = ::std::usize::MAX;
        for block in self.blocks.iter_mut() {
            block.idom = UNDEFINED;
            block.reachable = false;
        }
        let block_to_po = {
            let mut map = vec![0; self.blocks.len()];
            for (idx, &i) in rpo.iter().enumerate() {
                map[i] = rpo.len() - idx;
                self.blocks[i].reachable = true;
            }
            map[0] = rpo.len() + 1;
            map
        };
        self.blocks[0].reachable = true;
        self.blocks[0].idom = 0;
        loop {
            let mut changed = false;
            for &i in &rpo {
                // taken in part from petgraph
                let new_idom = {
                    let mut defined_preds = self.blocks[i].pred.iter().filter(|&&p| self.blocks[p].idom != UNDEFINED);
                    let first_pred = *defined_preds.next().unwrap();
                    defined_preds.fold(first_pred, |idom, &pred| {
                        // insersect function
                        let mut finger1: usize = idom;
                        let mut finger2: usize = pred;
                        while finger1 != finger2 {
                            if block_to_po[finger1] < block_to_po[finger2] {
                                finger1 = self.blocks[finger1].idom;
                            } else if block_to_po[finger2] < block_to_po[finger1] {
                                finger2 = self.blocks[finger2].idom;
                            }
                        }
                        finger1
                    })
                };
                if self.blocks[i].idom != new_idom {
                    self.blocks[i].idom = new_idom;
                    changed = true;
                }
            }
            if !changed { break; }
        }
    }

    fn detect_natural_loops(&mut self) -> Vec<Loop> {
        // identify back-edges
        let mut body = vec![];
        let mut stack = vec![];
        let mut loops = vec![];
        for h in 0..self.blocks.len() {
            body.clear();
            for i in 0..self.blocks[h].pred.len() {
                let n = self.blocks[h].pred[i];
                // check if h dominates n
                let dominates = {
                    let mut n = n;
                    loop {
                        if n == h {
                            break true;
                        }
                        if n == 0 {
                            break false;
                        }
                        n = self.blocks[n].idom;
                    }
                };
                if !dominates { continue; }
                body.push(h);
                stack.clear();
                stack.push(n);
                self.blocks[h].depth += 1;
                while let Some(d) = stack.pop() {
                    if body.contains(&d) { continue; }
                    body.push(d);
                    self.blocks[d].depth += 1;
                    stack.extend(self.blocks[d].pred.iter());
                }
            }
            if !body.is_empty() {
                loops.push(Loop {
                    header: h,
                    body: body.clone(),
                });
            }
        }
        loops
    }
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
    let retaddr = fac.create();
    let instructions = vec![
        IRInstruction::MovImm { dest: a, imm: 0 },
        IRInstruction::MovImm { dest: one, imm: 1 },
        IRInstruction::Label(loop_start),
        IRInstruction::Sub { dest: b, a: a, b: one },
        IRInstruction::Sub { dest: c, a: c, b: b },
        IRInstruction::Sub { dest: a, a: b, b: one },
        IRInstruction::CondJmp { cond: isa::JumpCondition::Zero, reg: a, target: loop_start.get_ref(), addr: label },
        IRInstruction::MovReg { dest: ret, src: c },
        IRInstruction::Ret { addr: retaddr, value: Some(ret) },
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
        BitSet::from_bytes(&[0b00001000]), // ret
        BitSet::from_bytes(&[0b00000000]),
    ]);
    // def: a     live: a, c
    // def: one   live: one, a, c
    //            live: one, a, c
    // def: b     live: one, b, c
    // def: c     live: one, b, c
    // def: a     live: one, a, c
    // def: label live: one, a, c
    // def: ret (move) live: ret
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
    expected.add_edge(ret, retaddr);
    assert_eq!(ig, expected);
}

#[test]
fn test_coloring() {
    let mut graph = InterferenceGraph::new(5);
    for i in 0..4 {
        for j in i+1..4 {
            graph.add_edge(i, j);
        }
    }
    let spill_costs = vec![100.0f32, 100.0, 0.0, 100.0, 100.0];
    graph.add_edge(0, 4);
    assert!(compute_graph_coloring(&graph, 4, &spill_costs).is_ok());
    assert_eq!(compute_graph_coloring(&graph, 3, &spill_costs),
        Err(vec![Temporary(2)]));
}

#[test]
fn test_cfg() {
    let mut fac = TemporaryFactory::new();
    let mut label_fac = LabelFactory::new();
    let loop_start = label_fac.create();
    let loop_end = label_fac.create();
    let one = fac.create();
    let a = fac.create();
    let b = fac.create();
    let c = fac.create();
    let ret = fac.create();
    let label = fac.create();
    let retaddr = fac.create();
    let instructions = vec![
        // 0: 0..2 -> 1
        IRInstruction::MovImm { dest: a, imm: 0 },
        IRInstruction::MovImm { dest: one, imm: 1 },
        IRInstruction::Label(loop_start),
        // 1: 3..6 -> 2, 3
        IRInstruction::Sub { dest: b, a: a, b: one },
        IRInstruction::Sub { dest: c, a: c, b: b },
        IRInstruction::CondJmp { cond: isa::JumpCondition::Zero, reg: b, target: loop_end.get_ref(), addr: label },
        // 2: 6..8 -> 1, 3
        IRInstruction::Sub { dest: a, a: b, b: one },
        IRInstruction::CondJmp { cond: isa::JumpCondition::Zero, reg: a, target: loop_start.get_ref(), addr: label },
        IRInstruction::Label(loop_end),
        // 3: 9..11 -> end
        IRInstruction::MovReg { dest: ret, src: c },
        IRInstruction::Ret { addr: retaddr, value: Some(ret) },
    ];
    let mut cfg = construct_cfg(&instructions, label_fac.count());
    assert_eq!(cfg, ControlFlowGraph { blocks: vec![
        BasicBlock { range: 0..2,  succ: vec![1],    reachable: true, pred: vec![],     idom: 0, depth: 0 },
        BasicBlock { range: 3..6,  succ: vec![2, 3], reachable: true, pred: vec![0, 2], idom: 0, depth: 0 },
        BasicBlock { range: 6..8,  succ: vec![1, 3], reachable: true, pred: vec![1],    idom: 0, depth: 0 },
        BasicBlock { range: 9..11, succ: vec![],     reachable: true, pred: vec![1, 2], idom: 0, depth: 0 },
    ] });
    cfg.compute_dominators();
    assert_eq!(cfg, ControlFlowGraph { blocks: vec![
        BasicBlock { range: 0..2,  succ: vec![1],    reachable: true, pred: vec![],     idom: 0, depth: 0 },
        BasicBlock { range: 3..6,  succ: vec![2, 3], reachable: true, pred: vec![0, 2], idom: 0, depth: 0 },
        BasicBlock { range: 6..8,  succ: vec![1, 3], reachable: true, pred: vec![1],    idom: 1, depth: 0 },
        BasicBlock { range: 9..11, succ: vec![],     reachable: true, pred: vec![1, 2], idom: 1, depth: 0 },
    ] });
    let loops = cfg.detect_natural_loops();
    assert_eq!(loops, vec![
        Loop { header: 1, body: vec![1, 2] },
    ]);
    assert_eq!(cfg, ControlFlowGraph { blocks: vec![
        BasicBlock { range: 0..2,  succ: vec![1],    reachable: true, pred: vec![],     idom: 0, depth: 0 },
        BasicBlock { range: 3..6,  succ: vec![2, 3], reachable: true, pred: vec![0, 2], idom: 0, depth: 1 },
        BasicBlock { range: 6..8,  succ: vec![1, 3], reachable: true, pred: vec![1],    idom: 1, depth: 1 },
        BasicBlock { range: 9..11, succ: vec![],     reachable: true, pred: vec![1, 2], idom: 1, depth: 0 },
    ] });
}
