grammar AbstractExecution;

@header {
package antlr.crowbar.gen;
}

// Whitespace and comments
WS           : [ \t\r\n\u000C]+ -> skip;
COMMENT      : '/*' .*? '*/' -> skip;

// Keywords
ACC : 'accessible';
ASS : 'assignable';
HAS : 'hasTo';
VAL : 'value';
REQ : 'requires';
RETB : 'return_behavior';
VAR :  'ae_specvars';
CON : 'ae_constraint';
FOR : 'formula';
LOC : 'locset';
DIS : 'disjoint';
MUT : 'mutex';

APE : 'abstract_expression';
APS : 'abstract_statement';

ANY : 'any';
EVERY : 'everything';
TRUE: 'true';
FALSE: 'false';

// Special symbols
DDOT : ':';
COMMA : ',';
LPAR : '(';
RPAR : ')';

// Strings
STRING : [a-zA-Z0-9]+ ;

// Entry Point, there is one global specification constraining all program and a local specification for every abstract placeholder element
entry : global                          # global_spec
      | local                           # local_spec
      ;

// The global specification introduces variables and constraints
global : VAR vars                       # vars_spec
       | CON phi                        # constraint_spec
       ;

// Variables introduced are either locations or fomula.
vars : LOC ids_loc                      # location_declaration
     | FOR formula_dec                  # formula_declaration
     ;

// List of location names
ids_loc : id_loc (COMMA id_loc)*;

// Name of a location
id_loc : EVERY | STRING ;

// List of formula declaration
formula_dec : simple_dec (COMMA simple_dec)*;

// Declaration of a formula
simple_dec : id_formula LPAR ANY RPAR;

// Name of a formula
id_formula : STRING ;

// A constraint can be locset being disjoint or a mutex between formula
phi : DIS LPAR ids_loc RPAR             # disjoint_constraint
    | MUT LPAR formula_list RPAR        # mutex_constraint
    ;

// List of instantiated formula
formula_list : formula (COMMA formula)* ;

// Instatiated formula
formula : id_formula VAL LPAR id_loc RPAR | TRUE | FALSE;

// Local specification can declare statement, expression, assignable, accessible and behavioral specification
local : APS aps_name                    # statement_local
      | APE ape_name                    # expression_local
      | ASS ass_list                    # assignable_local
      | ACC ids_loc                     # accessible_local
      | RETB REQ formula                # return_local
      ;

// Name of an abstrat statement
aps_name : STRING;

// Name of an abstract expression
ape_name : STRING;

// List of assignables
ass_list : assignable (COMMA assignable)*;

// Assignable is a potentially has_to locset
assignable : id_loc                     # simple_assignable
           | HAS LPAR id_loc RPAR       # hasTo_assignable
           ;