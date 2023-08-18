program_grammar = '''
    program
        = 'program' @:var '{'
                           @:states
                           @:env_events
                           @:con_events
                           @:prog_events
                           @:valuation
                           @:env_trans
                           @:con_trans
                        '}'
        ;

    states = @:'STATES' '{' @+:state {(',' | ';') @+:state}* '}';
    state = @:state_label [':' @:'init'];

    env_events
        =
        | @:'ENVIRONMENT EVENTS' '{' @:events '}'
        | @:'ENV EVENTS' '{' @:events '}'
        ;

    con_events
        =
        | @:'CONTROLLER EVENTS' '{' @:events '}'
        | @:'CON EVENTS' '{' @:events '}'
        ;

    prog_events
        =
        | @:'PROGRAM EVENTS' '{' @:events '}'
        | @:'PROG EVENTS' '{' @:events '}'
        ;

    events = @:var {(',' | ';') @:events}* ;

    valuation
        = @:'VALUATION' '{'
                @:valuation_atom {(',' | ';') @:valuation_atom}* [',' | ';']
                '}';

    valuation_atom = @:var ':' @:type ':=' @:(number | boolean);

    type = ('int' | 'bool' | 'real' | 'integer' | 'boolean' | 'rational' | 'natural');

    assignments
        = (@:var ':=' @:(math_expression | prop)) {(',' | ';') @:assignments}* [',' | ';'];

    env_trans
        = @:(('ENV' | 'ENVIRONMENT') 'TRANSITIONS') '{'
                { @+:env_trans_atom [',' | ';']}*
            '}';

    env_trans_atom
        = (@:state_label '->' @:state_label '[' @:prop [@:('$' assignments)] [@:('>>' events)]']');

    con_trans
        = @:{('CON' | 'CONTROLLER') 'TRANSITIONS'} '{'
                {(@+:con_trans_atom) [',' | ';']}*
            '}';

    con_trans_atom
        = (@:state_label '->' @:state_label '[' @:prop [@:('$' assignments)] ']');

    state_label = /[a-zA-Z0-9@\_\-]*/;
    var = /\_?[a-zA-Z][a-zA-Z0-9\_\-]*/;
'''