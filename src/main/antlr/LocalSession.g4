grammar LocalSession;

@header {
package antlr.crowbar.gen;
}

//Whitespace and comments
WS           : [ \t\r\n\u000C]+ -> skip;
COMMENT      : '/*' .*? '*/' -> skip;
//LINE_COMMENT : '//' ~[\r\n]* -> channel(HIDDEN) ;

//Keywords
SKIP_S : 'skip';
PUT : 'Put';
SUSP : 'Susp';
GET : 'Get';
THIS : 'this';


//Special symbols
AST : '*';
ALTERNATIVE : '+';
DOT : '.';
COMMA : ',';
OPARAN : '(';
CPARAN : ')';
BANG : '!';


AND : '&&';
OR : '||';

//Strings
// TODO: Identifiers could contain other chars
//       esp. for binary operators
STRING : [a-zA-Z0-9/\-_=<>]+ ;

//Entry point
local : local DOT local                               # seq_local_type
      | OPARAN local CPARAN                           # nested_local_type
      | local ALTERNATIVE local                       # or_local_type
      | OPARAN local CPARAN AST                       # rep_local_type
      | SKIP_S                                        # skip_local_type
      | PUT OPARAN formula CPARAN                     # put_local_type
      | SUSP OPARAN formula CPARAN                    # susp_local_type
      | GET OPARAN term CPARAN                        # get_local_type
      | role BANG STRING OPARAN formula CPARAN        # call_local_type
      ;

formula : BANG formula                                # not_type_formula
        | formula AND formula                         # and_type_formula
        | formula OR formula                          # or_type_formula
        | term                                        # boolean_type_formula
        ;

term : STRING OPARAN termlist CPARAN                  # function_type_term
     | THIS DOT STRING                                # field_type_term
     | term binop term                                # binary_type_term
     | STRING                                         # constant_type_term
     ;

termlist : term (COMMA term)*;

role : STRING;

binop : STRING | AST | ALTERNATIVE | BANG '=' | '==' | '=';