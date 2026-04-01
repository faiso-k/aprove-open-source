grammar InterprocInvariant;

options {
	backtrack = true;
}

@lexer::header { 
package aprove.input.Generated.InterprocInvariant;
}

@header {
package aprove.input.Generated.InterprocInvariant;

import java.util.LinkedList;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
}

interprocInvariant returns [TRSTerm t]
    :   r=boolExpression1 { t = r; };

intExpression returns [TRSTerm t]
	:	l=intExpression2 { t = l; }
			(
				 PLUS t2=intExpression2
					{
						t = TRSTerm.createFunctionApplication(FunctionSymbol.create("+", 2), t, t2);
					}
				|MINUS t2=intExpression2
					{
						t = TRSTerm.createFunctionApplication(FunctionSymbol.create("-", 2), t, t2);
					}
			)*;
	
intExpression2 returns [TRSTerm t]
	:	l=intExpression3 { t = l; }
			(
				 TIMES t2=intExpression3
					{
						t = TRSTerm.createFunctionApplication(FunctionSymbol.create("*", 2), t, t2);
					}
				|DIV t2=intExpression3
					{
						t = TRSTerm.createFunctionApplication(FunctionSymbol.create("/", 2), t, t2);
					}
			)*;

intExpression3 returns [TRSTerm t]
	:	i=INT { t = TRSTerm.createFunctionApplication(FunctionSymbol.create(i.getText(), 0)); }
	|	m=MINUS? i=INT? var=ID	
		{ 
			t = TRSTerm.createVariable(var.getText()); 
			if (m != null) { 
				t = TRSTerm.createFunctionApplication(
						FunctionSymbol.create("*", 2), 
						TRSTerm.createFunctionApplication(FunctionSymbol.create("-1", 0)),
						t); 
			}
			if (i != null) {
				t = TRSTerm.createFunctionApplication(
						FunctionSymbol.create("*", 2), 
						TRSTerm.createFunctionApplication(FunctionSymbol.create(i.getText(), 0)),
						t);
			}
		 }
	|	LPAR s=intExpression RPAR { t = s; };

boolExpression1 returns [TRSTerm t]
	:	b=boolExpression2 { t = b; } (AND newT=boolExpression2 {t = IDPv2ToIDPv1Utilities.getConjunction(t, newT); } )*;
	
boolExpression2 returns [TRSTerm t]
	:	l=intExpression o=COMP r=intExpression 
			{
				t = TRSTerm.createFunctionApplication(FunctionSymbol.create(o.getText(), 2), l, r);
			}
	
	|	LPAR b=boolExpression1 RPAR { t = b; };


// lexical stuff below


PLUS	:	'+';
MINUS	:	'-';
TIMES	:	'*';
DIV	:	'/';
AND	:	';';
LPAR 	:	'(';
RPAR	:	')';
COMP	:	'<' | '<=' | '=' | '!=' | '>=' | '>';

ID  :	('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_')*
    ;

INT :	'0'..'9'+
    ;

WS  :   ( ' '
        | '\t'
        | '\r'
        | '\n'
        ) {$channel=HIDDEN;}
    ;

