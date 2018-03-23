# CFG syntax

    program -> program global .
    program -> .

    global -> global_decl .
    global -> func .

    global_decl -> GLOBAL IDENTIFIER SEMICOLON .

    func -> IDENTIFIER LPAREN args RPAREN statement .

    args -> IDENTIFIER args .
    args -> .

    statement -> expr SEMICOLON .
    statement -> LBRACE statements RBRACE .
    statement -> IF LPAREN expr RPAREN statement .
    statement -> WHILE LPAREN expr RPAREN statement .
    statement -> RETURN optional_expr SEMICOLON .
    statement -> BREAK SEMICOLON .
    statement -> CONTINUE SEMICOLON .
    statement -> PRINT STRING .

    optional_expr -> expr .
    optional_expr -> .

    statements -> statement  statements .
    statements -> .

    expr -> expr1 .

# Types

All variables are `u16`s.

Global variables exist at top level, locals at local level. Implicit declaration.

Functions return implicit `u16` that's undefined if no return.

Print statement is a statement that can print strings.

# Registers

| Register | Usage                         |
--------------------------------------------
| r0       | Unused (zero register)        |
| r1       | Return value of function      |
| r1-r7    | Parameters to function        |
| r1-r14   | Free (caller-saved)           |
| r15      | Stack Pointer                 |

# Control flow

Functions can have tops 6 args, have a main entrypoint.
