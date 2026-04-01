grammar T2IntSys;

options {
	backtrack = true;
}

@lexer::header { 
package aprove.input.Generated.T2IntSys;
}

@header {
package aprove.input.Generated.T2IntSys;

import java.util.LinkedList;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap.*;

import aprove.input.Programs.t2.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
}

t2IntSys returns [T2IntSys t2Sys = new T2IntSys()]
	:	start[t2Sys] 
		( 
			  trans=transition {t2Sys.addTransition(trans);} 
			| SHADOW LPAR (~')')+ RPAR SEM
		)*;

start[T2IntSys t2Sys]	
	: START COLON id=stateid SEM
	{
		t2Sys.setStartState(id);
	}
	  (ERROR COLON stateid SEM)?
	  (CUTPOINT COLON stateid SEM)?;


transition returns [T2IntTrans trans]
	@init { List<T2IntTransBodyStatement> statements = new LinkedList<>(); }
	:
		fromState=from 
			(
				 assign=assignment {statements.add(assign);} 
				|assump=assumption {statements.add(assump);}
			)*
		toState=to
		{ trans = new T2IntTrans(fromState, toState, statements); };
	
from returns [int i]
	:	FROM COLON si=stateid SEM { i = si; };

to returns [int i]
	:	TO COLON si=stateid SEM { i = si; };

stateid returns [int i]
	:	intString=INT
	{
		i = Integer.parseInt(intString.getText());
	};

assignment returns [T2IntTransAssignment ass]
	:	(AT LPAR INT COMMA STRING RPAR)? var=ID COLONEQ val=intExpression SEM { ass = new T2IntTransAssignment(TRSTerm.createVariable(var.getText()), val); };

assumption returns [T2IntTransGuard guard]
	:	  (AT LPAR INT COMMA STRING RPAR)? ASSUME LPAR c=boolExpression RPAR SEM { guard = new T2IntTransGuard(c); }
		| (AT LPAR INT COMMA STRING RPAR)? ASSUME LPAR v=ID RPAR SEM { guard = new T2IntTransGuard(TRSTerm.createFunctionApplication(FunctionSymbol.create("!=", 2), TRSTerm.createVariable(v.getText()), TRSTerm.createFunctionApplication(FunctionSymbol.create("0", 0)))); };
	

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
                |REM t2=intExpression3
                    {
                        t = TRSTerm.createFunctionApplication(FunctionSymbol.create("\%", 2), t, t2);
                    }
			)*;

intExpression3 returns [TRSTerm t]
	:	i=INT { t = TRSTerm.createFunctionApplication(FunctionSymbol.create(i.getText(), 0)); }
	|	MINUS i=INT { t = TRSTerm.createFunctionApplication(FunctionSymbol.create("-" + i.getText(), 0)); }
	|	MINUS? NONDET LPAR RPAR { t = TRSTerm.createFunctionApplication(FunctionSymbol.create("nondet", 0)); }
	|	LPAR s=intExpression RPAR { t = s; }
	|	var=ID	{ t = TRSTerm.createVariable(var.getText()); }
    |   MINUS var=ID { t =  TRSTerm.createFunctionApplication(FunctionSymbol.create("*", 2), TRSTerm.createFunctionApplication(FunctionSymbol.create("-1", 0)), TRSTerm.createVariable(var.getText())); };

boolExpression returns [TRSTerm t]
	:	b=boolExpression2 { t = b; } (OR newT=boolExpression {t = IDPv2ToIDPv1Utilities.getDisjunction(t, newT); } )?;
	
boolExpression2 returns [TRSTerm t]
	:	b=boolExpression3 { t = b; } (AND newT=boolExpression2 {t = IDPv2ToIDPv1Utilities.getConjunction(t, newT); } )?;
	
boolExpression3 returns [TRSTerm t]
	:	TRUE 
			{ 
				t = TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE",0)); 
			}
	| 	FALSE 
			{ 
				t = TRSTerm.createFunctionApplication(FunctionSymbol.create("FALSE",0));
			}
	|	l=intExpression o=COMP r=intExpression 
			{
                String funName = o.getText();
				if ("==".equals(funName)) {
					funName = "=";
				}
				t = TRSTerm.createFunctionApplication(FunctionSymbol.create(funName, 2), l, r);
			}
	
	|	LPAR b=boolExpression RPAR { t = b; }
	|	NOT LPAR b=boolExpression RPAR { t = TRSTerm.createFunctionApplication(FunctionSymbol.create("!", 1), b); };


// lexical stuff below


PLUS	:	'+';
MINUS	:	'-';
TIMES	:	'*';
DIV	:	'/';
REM	:	'%';
AND	:	'&&';
OR	:	'||';
LPAR 	:	'(';
RPAR	:	')';
NOT		:	'!';
NONDET	:	'nondet';
ASSUME	:	'assume';
AT		:	'AT';
TRUE	:	'true';
FALSE	:	'false';
FROM	:	'FROM';
TO	:	'TO';
START	:	'START';
ERROR   :   'ERROR';
CUTPOINT    :   'CUTPOINT';
SHADOW	:	'SHADOW';
COMMA	:	',';
SEM	:	';';
COLON	:	':';
COLONEQ	:	':=';
COMP	:	'<' | '<=' | '==' | '=' | '!=' | '>=' | '>';

ID  :	('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_')*
    ;

INT :	'0'..'9'+
    ;


COMMENT
    :   '//' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;}
    |   '/*' ( options {greedy=false;} : . )* '*/' {$channel=HIDDEN;}
    ;

STRING	:	'"' ( options {greedy=false;} : . )* '"';

WS  :   ( ' '
        | '\t'
        | '\r'
        | '\n'
        ) {$channel=HIDDEN;}
    ;
