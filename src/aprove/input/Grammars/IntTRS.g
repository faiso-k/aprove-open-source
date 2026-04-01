grammar IntTRS;

options {
	backtrack = true;
}

@lexer::header { 
package aprove.input.Generated.IntTRS;
}

@header {
package aprove.input.Generated.IntTRS;

import immutables.*;
import java.util.Set;
import java.util.LinkedHashSet;
import java.util.ArrayList;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IntTRS.*;
}

intTRS returns [IRSwTProblem p]
	@init { 
		Set<IGeneralizedRule> rules = new LinkedHashSet<>();
	}
	:	(startTerm=startT)?
		irule[rules]*
	{	p = new IRSwTProblem(ImmutableCreator.create(rules), startTerm); };


startT returns [TRSFunctionApplication f]
	:	START	r=functionApp { f = r; } (c=condition)?;
	
irule[Set<IGeneralizedRule> rules]
	:	l=functionApp TO r=functionApp (c=condition)? { rules.add(IGeneralizedRule.create(l, r, c)); };
		

functionApp returns [TRSFunctionApplication f]
    @init { ArrayList<TRSTerm> args = new ArrayList<>(); }
    :   fs=ID
        (
            LPAR RPAR
        |   LPAR
            (
                ( fa = functionApp { args.add(fa); } | t = intExpression { args.add(t); } )
                COMMA
            )*
            ( fa = functionApp { args.add(fa); } | t = intExpression { args.add(t); } )
            RPAR
        )
        { f = TRSTerm.createFunctionApplication(
                FunctionSymbol.create(fs.getText(), args.size()),
                ImmutableCreator.create(args));
        };
		
condition returns [TRSTerm c]
	:
		(
		     LBRACK
		     t=boolExpression { c = t; }
		     RBRACK
		    |
		     CONDSEP
             t=boolExpression { c = t; }
        );

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
				|MOD t2=intExpression3
					{
						t = TRSTerm.createFunctionApplication(FunctionSymbol.create("\%", 2), t, t2);
					}
			)*;

intExpression3 returns [TRSTerm t]
	:	i=INT { t = TRSTerm.createFunctionApplication(FunctionSymbol.create(i.getText(), 0)); }
    |   m=MINUS i=INT { t = TRSTerm.createFunctionApplication(FunctionSymbol.create("-" + i.getText(), 0)); }
	|	m=MINUS? var=ID (EXP e=INT)?
		{
			t = TRSTerm.createVariable(var.getText());
			if (e != null) {
				int exp = Integer.valueOf(e.getText());
				assert (exp >= 0) : "Exponent < 1 not allowed";
				TRSTerm baseT = t;
				while (exp > 1) {
					t = TRSTerm.createFunctionApplication(
							FunctionSymbol.create("*", 2),
							baseT,
							t);
					exp--;
				}
			}
			if (m != null) {
				t = TRSTerm.createFunctionApplication(
						FunctionSymbol.create("*", 2),
						TRSTerm.createFunctionApplication(FunctionSymbol.create("-1", 0)),
						t);
			}
        }
	|	LPAR s=intExpression RPAR { t = s; };

boolExpression returns [TRSTerm t]
	:	b=boolExpression2 { t = b; } ((AND|AND2) newT=boolExpression2 {t = IDPv2ToIDPv1Utilities.getConjunction(t, newT); } )*;
	
boolExpression2 returns [TRSTerm t]
	:	TRUE 
			{ 
				t = TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE",0)); 
			}
	| 	FALSE 
			{ 
				t = TRSTerm.createFunctionApplication(FunctionSymbol.create("FALSE",0));
			}
	|	o=NOT r=boolExpression2
			{
				t = TRSTerm.createFunctionApplication(FunctionSymbol.create(o.getText(), 1), r);
			}
	|	l=intExpression o=COMP r=intExpression 
			{
				t = TRSTerm.createFunctionApplication(FunctionSymbol.create(o.getText(), 2), l, r);
			}

	
	|	LPAR b=boolExpression RPAR { t = b; };


// lexical stuff below


PLUS	:	'+';
MINUS	:	'-';
TIMES	:	'*';
MOD	:	'%';
DIV	:	'/';
EXP	:	'^';
LPAR 	:	'(';
RPAR	:	')';
RBRACK	:	']';
LBRACK 	:	'[';
TO	:	'->';
COMMA	:	',';
AND	:	'/\\';
AND2 :   '&&';
COMP	:	'<' | '<=' | '=' | '!=' | '>=' | '>' ;
NOT		: 	'!';
TRUE	:	'TRUE';
FALSE	:	'FALSE';
CONDSEP :   ':|:';
START	: 'Start:';


COMMENT
    :   '///***' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;}
    ;

ID  :	('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|'.'|'\'')*
    ;

INT :	'0'..'9'+
    ;

WS  :   ( ' '
        | '\t'
        | '\r'
        | '\n'
        ) {$channel=HIDDEN;}
    ;
