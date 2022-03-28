grammar AbstractExecution;

@header {
package antlr.crowbar.gen;
}

//Whitespace and comments
WS           : [ \t\r\n\u000C]+ -> skip;
COMMENT      : '/*' .*? '*/' -> skip;

//Help
NUM : [0-9]+ ;
ANN : 'AnnotationOuiOui';

//False Entry Point for now.

entry : ANN;