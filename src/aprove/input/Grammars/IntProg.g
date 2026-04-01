/*   Type:        ANTLR
 *   Title:       Grammar for C Integer Programs
 *   Description: A grammar definiton for C integer programs
 *   Project:     AProVE
 *   Authors:     Thomas Str�der
 *   Copyright:   Copyright (c) 2015
 *   Department:  RWTH Aachen / Templergraben 55 / D-52056 Aachen
 */

grammar IntProg;

options {
    language=Java;
}

@header{
package aprove.input.Generated.IntProg;

import immutables.*;
import java.util.ArrayList;
import java.util.Set;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.LinkedHashMap;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.input.Programs.intProg.*;
}

// lexer imports
@lexer::header{
package aprove.input.Generated.IntProg;

import aprove.input.Programs.intProg.*;
}

@lexer::members {
  @Override
  public void reportError(RecognitionException e) {
    throw new IntProgParseException(e);
  }
}

// global member variable for global requests
@members{
int fresh_fun_sym = 1; // used to create fresh function symbols
int fresh_var = 1; // used to create fresh variables
Set<IGeneralizedRule> rules = new LinkedHashSet<>();
Map<String, TRSVariable> vars = new LinkedHashMap<>();
ImmutableArrayList<TRSTerm> def_args = null;

@Override
public void reportError(RecognitionException e) {
    throw new IntProgParseException(e);
}
}

// parser rules (start with lowercase letter, must not contain literals)

nondet : NONDETNAME W* OPENP W* CLOSEP;

num_atom returns [TRSTerm t] :
    (i=ZERO | i=POS) {t = TRSTerm.createFunctionApplication(FunctionSymbol.create(i.getText(), 0));}
  | nondet {t = TRSTerm.createVariable("x_" + fresh_var++);}
  | var=V
    {vars.containsKey(var.getText())}?
    {t = vars.get(var.getText());}
  | OPENP
    W*
    exp=bool_expr
    W*
    CLOSEP
    {t = exp;};

mult_expr returns [TRSTerm t] :
    left=num_atom
    (
        W*
        MULT
        W*
        right=num_atom
        {left = TRSTerm.createFunctionApplication(FunctionSymbol.create("*", 2), left, right);}
    )*
    {t = left;};

num_expr returns [TRSTerm t] :
    left=mult_expr
    (
        W*
        (op=PLUS | op=MINUS)
        W*
        right=mult_expr
        {left = TRSTerm.createFunctionApplication(FunctionSymbol.create(op.getText(), 2), left, right);}
    )*
    {t = left;}
  | MINUS
    W*
    left=mult_expr
    {
        left =
            TRSTerm.createFunctionApplication(
                FunctionSymbol.create("-", 2),
                TRSTerm.createFunctionApplication(FunctionSymbol.create("0", 0)),
                left
            );
    }
    (
        W*
        (op=PLUS | op=MINUS)
        W*
        right=mult_expr
        {left = TRSTerm.createFunctionApplication(FunctionSymbol.create(op.getText(), 2), left, right);}
    )*
    {t = left;};

bool_atom returns [TRSTerm t] :
    TRUE {t = TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE", 0));}
  | FALSE {t = TRSTerm.createFunctionApplication(FunctionSymbol.create("FALSE", 0));}
  | left=num_expr
    {t = left;}
    (
        W*
        op=BO
        W*
        right=num_expr
        {
            t =
                TRSTerm.createFunctionApplication(
                    FunctionSymbol.create(op.getText().equals("==") ? "=" : op.getText(), 2),
                    left,
                    right
                );
        }
    )?;

and_expr returns [TRSTerm t] :
    left=bool_atom
    (
        W*
        AND
        W*
        right=bool_atom
        {left = TRSTerm.createFunctionApplication(FunctionSymbol.create("&&", 2), left, right);}
    )*
    {t = left;};

bool_expr returns [TRSTerm t] :
    left=and_expr
    (
        W*
        OR
        W*
        right=and_expr
        {left = TRSTerm.createFunctionApplication(FunctionSymbol.create("||", 2), left, right);}
    )*
    {t = left;}
  | NOT
    W*
    exp=bool_atom
    {t = TRSTerm.createFunctionApplication(FunctionSymbol.create("!", 1), exp);};

loop[FunctionSymbol start] returns [FunctionSymbol end]
@init{
    FunctionSymbol check = null;
} : WHILE
    W*
    OPENP
    W*
    cond=bool_expr
    W*
    CLOSEP
    W*
    OPENC
    W*
    (
        {check = FunctionSymbol.create("f" + fresh_fun_sym++, vars.size());}
        middle=instructions[check]
        W*
        CLOSEC
        {
            end = FunctionSymbol.create("f" + fresh_fun_sym++, vars.size());
            rules.add(
                IGeneralizedRule.create(
                    TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                    TRSTerm.createFunctionApplication(check, ImmutableCreator.create(def_args)),
                    cond
                )
            );
            rules.add(
                IGeneralizedRule.create(
                    TRSTerm.createFunctionApplication(middle, ImmutableCreator.create(def_args)),
                    TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                    TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE", 0))
                )
            );
            rules.add(
                IGeneralizedRule.create(
                    TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                    TRSTerm.createFunctionApplication(end, ImmutableCreator.create(def_args)),
                    TRSTerm.createFunctionApplication(FunctionSymbol.create("!", 1), cond)
                )
            );
        }
    |
        CLOSEC
        {
            end = FunctionSymbol.create("f" + fresh_fun_sym++, vars.size());
            rules.add(
                IGeneralizedRule.create(
                    TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                    TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                    cond
                )
            );
            rules.add(
                IGeneralizedRule.create(
                    TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                    TRSTerm.createFunctionApplication(end, ImmutableCreator.create(def_args)),
                    TRSTerm.createFunctionApplication(FunctionSymbol.create("!", 1), cond)
                )
            );
        }
    );

condition[FunctionSymbol start] returns [FunctionSymbol end]
@init{
    FunctionSymbol tbranch = null;
    FunctionSymbol fbranch = null;
    FunctionSymbol fend = null;
} : IF
    W*
    OPENP
    W*
    cond=bool_expr
    W*
    CLOSEP
    {
        tbranch = FunctionSymbol.create("f" + fresh_fun_sym++, vars.size());
        fbranch = FunctionSymbol.create("f" + fresh_fun_sym++, vars.size());
        end = FunctionSymbol.create("f" + fresh_fun_sym++, vars.size());
        fend = fbranch;
    }
    W*
    OPENC
    W*
    (
        tend=instructions[tbranch]
        W*
        CLOSEC
    |
        CLOSEC
        {tend = tbranch;}
    )
    (
        W*
        ELSE
        W*
        OPENC
        W*
        (
            fendsym=instructions[fbranch]
            W*
            CLOSEC
            {fend = fendsym;}
        |
            CLOSEC
        )
    )?
    {
        rules.add(
            IGeneralizedRule.create(
                TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                TRSTerm.createFunctionApplication(tbranch, ImmutableCreator.create(def_args)),
                cond
            )
        );
        rules.add(
            IGeneralizedRule.create(
                TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                TRSTerm.createFunctionApplication(fbranch, ImmutableCreator.create(def_args)),
                TRSTerm.createFunctionApplication(FunctionSymbol.create("!", 1), cond)
            )
        );
        rules.add(
            IGeneralizedRule.create(
                TRSTerm.createFunctionApplication(tend, ImmutableCreator.create(def_args)),
                TRSTerm.createFunctionApplication(end, ImmutableCreator.create(def_args)),
                TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE", 0))
            )
        );
        rules.add(
            IGeneralizedRule.create(
                TRSTerm.createFunctionApplication(fend, ImmutableCreator.create(def_args)),
                TRSTerm.createFunctionApplication(end, ImmutableCreator.create(def_args)),
                TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE", 0))
            )
        );
    };

assignment[FunctionSymbol start] returns [FunctionSymbol end] :
    name=V
    W*
    ASSIGN
    {vars.containsKey(name.getText())}?
    W*
    exp=num_expr
    W*
    TERMINATOR
    {
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        for (Map.Entry<String, TRSVariable> entry : vars.entrySet()) {
            if (name.getText().equals(entry.getKey())) {
                args.add(exp);
            } else {
                args.add(entry.getValue());
            }
        }
        end = FunctionSymbol.create("f" + fresh_fun_sym++, args.size());
        rules.add(
            IGeneralizedRule.create(
                TRSTerm.createFunctionApplication(start, ImmutableCreator.create(def_args)),
                TRSTerm.createFunctionApplication(end, ImmutableCreator.create(args)),
                TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE", 0))
            )
        );
    };

instruction[FunctionSymbol start] returns [FunctionSymbol end] :
    (other=loop[start] | other=condition[start] | other=assignment[start])
    {end = other;};

single_declaration :
    name=V
    {vars.put(name.getText(), TRSTerm.createVariable(name.getText()));};

declaration :
    INT
    W+
    single_declaration
    (W* COMMA W* single_declaration)*
    W*
    TERMINATOR;

declarations :
    declaration (W* declarations)?;

instructions[FunctionSymbol start] returns [FunctionSymbol end] :
    middle=instruction[start] {end=middle;}
    (W* other=instructions[middle])?
    {if (other != null) {end=other;}};

pre :
    W*
    TYPEDEF
    W+
    ENUM
    W*
    OPENC
    W*
    FALSE
    W*
    COMMA
    W*
    TRUE
    W*
    CLOSEC
    W*
    BOOL
    W*
    TERMINATOR
    W*
    EXTERN
    W+
    INT
    W+
    NONDETNAME
    W*
    OPENP
    W*
    VOID
    W*
    CLOSEP
    W*
    TERMINATOR
    W*
    INT
    W+
    MAIN
    W*
    OPENP
    W*
    CLOSEP
    W*
    OPENC;

post : RETURN W+ ZERO W* TERMINATOR W* CLOSEC W*;

irs returns [IRSProblem p]
@init{
    FunctionSymbol start = null;
} : pre
    (W* declarations)?
    {
        start = FunctionSymbol.create("f" + fresh_fun_sym++, vars.size());
        def_args = ImmutableCreator.create(new ArrayList<TRSTerm>(vars.values()));
    }
    (W* instructions[start])?
    W*
    post
    {
        p =
            new IRSProblem(
                ImmutableCreator.create(rules),
                TRSTerm.createFunctionApplication(start, def_args)
            );
    };


// Lexer rules (start with uppercase letter, must not have arguments, returns, or local variables)

INT : 'int';
IF : 'if';
WHILE : 'while';
ELSE : 'else';
TERMINATOR : ';';
OPENP : '(';
CLOSEP : ')';
OPENC : '{';
CLOSEC : '}';
MULT : '*';
MINUS : '-';
PLUS : '+';
BO : '<=' | '>=' | '<' | '>' | '==' | '!=';
ASSIGN : '=';
NONDETNAME : '__VERIFIER_nondet_int';
OR : '||';
AND : '&&';
NOT : '!';
TRUE : 'true';
FALSE : 'false';
TYPEDEF : 'typedef';
ENUM : 'enum';
COMMA : ',';
BOOL : 'bool';
EXTERN : 'extern';
VOID : 'void';
MAIN : 'main';
RETURN : 'return';
ZERO : '0';
POS : NONZERO DIGIT*;
fragment NONZERO : '1'..'9';
fragment DIGIT : ZERO | NONZERO;
V : CHAR ALPHANUM*;
fragment ALPHANUM : CHAR | DIGIT;
fragment CHAR : LOW | UP;
fragment LOW : 'a'..'z';
fragment UP: 'A'..'Z';
W : ' ' | '\n' | '\r' | '\t';
BLOCKCOMMENT : '/*' (.)* '*/' {$channel=HIDDEN;};
LINECOMMENT : '//' (~('\r'|'\n'))* {$channel=HIDDEN;};
