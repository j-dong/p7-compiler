#[derive(Debug, Clone)]
pub enum Global {
    GlobalVariable(String),
    Function(String, Vec<String>, Statement),
}

#[derive(Debug, Clone)]
pub enum Statement {
    ExprStatement(Box<Expr>),
    BlockStatement(Vec<Statement>),
    IfStatement { cond: Box<Expr>, body: Box<Statement> },
    WhileStatement { cond: Box<Expr>, body: Box<Statement> },
    ReturnStatement(Option<Box<Expr>>),
    BreakStatement,
    ContinueStatement,
    PrintStatement(String),
}

#[derive(Debug, Clone)]
pub enum Expr {
    AssignExpr(String, Box<Expr>),
    Plus(Box<Expr>, Box<Expr>),
    Minus(Box<Expr>, Box<Expr>),
    Variable(String),
    Constant(i16),
}
