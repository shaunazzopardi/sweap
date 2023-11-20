# TODO add a proper LTL parser
GRAMMAR = '''
@@grammar::POPL
@@keyword :: assert assume else enum extern false if intern method true
@@eol_comments :: /\/\/.*?$/

start::Program =
    { decls+:global_decl | enums+:enum_def }*
    methods:{ method }+
    [
        'assume' '{'
            assumes:{ ?'[^}]*' }
        '}'
    ]
    [
        'guarantee' '{'
            guarantees:{ ?'[^}]*' }
        '}'
    ]
    $
    ;

enum_def::EnumDef =
    'enum' ~ name:identifier '{'  cases:','.{identifier}+ '}' ';'
    ;

decl::Decl =
    var_type:identifier var_name:identifier ':=' init:expression ';'
    ;

global_decl::Decl
    =
    [io:'output'] >decl
    ;

signature =
    name:identifier '(' params:','.{ parameter }* ')'
    ;

parameter::Decl = var_type:identifier var_name:identifier init:()
    ;

method_modality = 'GF' | 'G' | 'F' | '!FG' ;

method::MethodDef =
    'method'
    modalities:{ method_modality }
    kind:( 'extern' | 'intern' ) ~ >signature '{'
    { assumes+:assumption | asserts+:assertion }*
    decls: { decl }*
    body:{ statement }*
    '}'
    node_type:`method_extern`
    ;

assumption = 'assume' '(' @:expression ')' ';' ;
assertion = 'assert' '(' @:expression ')' ';' ;

statement =
    | if
    | '{' @:{ statement }* '}'
    | assignment
    | incr
    | decr
    ;

incr::Increment = var_name:lhs '++' ';' ;
decr::Decrement = var_name:lhs '--' ';' ;

assignment::Assign = lhs:lhs ':=' rhs:expression ';' ;

if::If =
    'if' ~ '(' cond:expression ')'
    body:statement
    ['else' or_else:statement]
    ;

lhs::Store = name:identifier ;

expression
    =
    | binary_logic_expr
    | comparison
    ;

binary_logic_op = '&&' | '||' | '->' ;

binary_logic_expr::BinLogic
    =
    left:expression op:binary_logic_op ~ right:comparison
    ;

comparison
    =
    | compare_op
    | arithmetic
    ;

compare_op::Comparison
    =
    left:arithmetic op:('>='|'<='|'>'|'<'|'=='|'!=') ~ right:arithmetic
    ;

arithmetic
    =
    | add_or_sub
    | term
    ;

add_or_sub::BinOp
    =
    | left:arithmetic op:'+' ~ right:term
    | left:arithmetic op:/-(?!>)/ ~ right:term
    ;

term
    =
    | mul_or_div
    | factor
    ;

mul_or_div::BinOp
    =
    | left:term op:'*' right:factor
    | left:term op:'/' right:factor
    ;

factor
    =
    | unary
    | base_expr
    ;

unary::UnaryOp
    =
    | op:'!' ~ expr:base_expr
    | op:/-(?!>)/ expr:base_expr
    ;

base_expr
    =
    | '(' ~ @:expression ')'
    | bool_lit
    | number_lit
    | var_reference
    ;

var_reference::Load = name:identifier ;

@name
identifier = /[a-zA-Z][a-zA-Z0-9\_]*/;

bool_lit::Literal = value:(true|false) ;
true::bool = 'true' ;
# For false, we use @:() to return None
# so that bool(None) gives us False
false::bool = 'false' ~ @:() ;

number_lit::Literal = value:number ;
number::int = /[0-9]+/ ;
'''
