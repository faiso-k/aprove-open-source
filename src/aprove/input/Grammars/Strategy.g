grammar Strategy;

options {
    language = Java;
}

@header {
package aprove.input.Generated.Strategy;

import aprove.input.Programs.Strategy.*;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.ArrayList;
import java.util.logging.Logger;

}

@members {
    @Override
    public void reportError(RecognitionException e) {
        throw new StrategyParseException(e, this);
    }
}


@lexer::header {
package aprove.input.Generated.Strategy;

import aprove.input.Programs.Strategy.StrategyParseException;
}

@lexer::members {
    @Override
    public void reportError(RecognitionException e) {
        throw new StrategyParseException(e, this);
    }
}

/* Fragments are parts of tokens */
fragment Char: Lchar | Uchar | Digit | '_';
fragment Digit: ('0'..'9');
fragment Lchar: ('a'..'z');
fragment Nondq: ~('"');
fragment Uchar: ('A'..'Z');


/* Ignored tokens */
BACKSLASHNEWLINE: ('\\\n'|'\\\r\n')+
    { $channel = HIDDEN; };
COMMENT: ('#' (~'\n')* '\n' )+
    { $channel = HIDDEN; } ;
WHITESPACE: ('\t'|' '|'\r'|'\n'|'\u000C')+
    { $channel = HIDDEN; };


/* Regular tokens */
// uppercase keywords and uppercase identifiers
Repeat: 'Repeat';
RepeatS: 'RepeatS';
Timer: 'Timer';
WallTimer: 'WallTimer';
Delay: 'Delay';
AnyDelay: 'AnyDelay';
AnyK: 'AnyK';
Uname: Uchar Char*;

// lowercase keywords and uppercase identifiers
LC_defaults: 'defaults';
LC_let: 'let';
LC_declare: 'declare';
LC_import: 'import';
Lname: Lchar Char*;

NumberLit: '-'? Digit+;
StringLit: '"' Nondq* '"';


/* Grammar rules */


strategy returns [RawModule rm = new RawModule()]
    : imports[rm]* (let[rm]|declare[rm])* EOF
;

imports[RawModule rm]
    : LC_import n=lname {
        rm.addImport(n, n);
    }
;

declare[RawModule rm]
    : LC_declare n=uname '=' cn=classname (LC_defaults p=params)? {
        rm.addClassDecl(n, cn, p);
    }
;

classname returns [String cn]
    @init {
        StringBuilder sb = new StringBuilder();
    }
    : n=name cn_tail[sb]* {
        cn = n + sb.toString();
    }
;

cn_tail[StringBuilder sb]
    : '.' n=name {
        sb.append('.').append(n);
    }
;

let[RawModule rm]
    : LC_let? n=lname '=' exp=expression {
        rm.addLetDecl(n, exp);
    }
;

expression returns [StrategyExpression e]
    : e1=unaryExpression t=exprTail[e1] {
        e = t;
    }
;

exprTail[StrategyExpression e1] returns [StrategyExpression e]
    : ':' e2=expression {
        e = ExpressionFactory.sequence(e1, e2);
    }
    | ';' e2=expression {
        e = ExpressionFactory.parSequence(e1, e2);
    }
    | {
        e = e1;
    }
;

unaryExpression returns [StrategyExpression e]
    : exp=baseExpression o=unaryOp[exp] {
        e = o;
    }
;

unaryOp[StrategyExpression in] returns [StrategyExpression out]
    : '*' {
        out = ExpressionFactory.star(in);
    }
    | '+' {
        out = ExpressionFactory.plus(in);
    }
    | '?' {
        out = ExpressionFactory.question(in);
    }
    | {
        out = in;
    }
;

baseExpression returns [StrategyExpression e]
    : n=lname /* spars=sparams? */ {
        e = ExpressionFactory.letRef(n);
    }
    | n=uname pars=params? spars=sparams? {
        e = ExpressionFactory.classRef(n, pars, spars);
    }
    /* special cases */
    | Repeat '(' min=number ',' max=numberOrStar ',' exp = expression ')' {
        e = ExpressionFactory.repeat(min, max, exp);
    }
    | RepeatS '(' min=number ',' max=numberOrStar ',' exp = expression ')' {
        e = ExpressionFactory.repeatS(min, max, exp);
    }
    | Timer '(' t=number ',' exp = expression ')' {
        e = ExpressionFactory.timer(t, exp);
    }
    | WallTimer '(' t=number ',' exp = expression ')' {
        e = ExpressionFactory.wallTimer(t, exp);
    }
    | Delay '(' t=number ',' exp = expression ')' {
        e = ExpressionFactory.delay(t, exp);
    }
    | AnyDelay '(' t=number ',' el = expressionList ')' {
        e = ExpressionFactory.anyDelay(t, el);
    }
    | AnyK '(' k=number ',' el = expressionList ')' {
        e = ExpressionFactory.anyK(k, el);
    }
    | '(' exp=expression ')' {
        e = exp;
    }
;

numberOrStar returns [int i]
    : '*' {
        i = -1;
    }
    | n=number {
        i = n;
    }
;

sparams returns [List<StrategyExpression> params]
    : '(' el=expressionList ')' {
        params = el;
    }
;

expressionList returns [List<StrategyExpression> params = new ArrayList<StrategyExpression>()]
    : (addExpression[params] (',' addExpression[params])* )?
;

addExpression[List<StrategyExpression> list]
    : e=expression {
        list.add(e);
    }
;

params returns [Parameters p]
    : '[' rawpars=paramList ']' {
        p = ParameterFactory.fromMap(rawpars);
    }
    | '[' ']' {
        p = ParameterFactory.empty();
    }
;

paramList returns [Map<String, Value> rawpars = new LinkedHashMap<String, Value> ()]
    : assign[rawpars] (',' assign[rawpars])*
;

assign[Map<String, Value> rawpars]
    : id=identifier '=' v=value {
        rawpars.put(id, v);
    }
;

identifier returns [String id]
    : s=uname {
        id = s;
    }
;

value returns [Value v]
    : c = complexValue {
        v = c;
    }
    | n=number {
        v = ParameterFactory.number(n);
    }
    | s=string {
        v = ParameterFactory.literalString(s);
    }
;

complexValue returns [Value c]
    : id=identifier p=params? {
        c = ParameterFactory.callValue(id, p);
    }
;


number returns [Integer i]
    : n=NumberLit {
        i = Integer.parseInt(n.getText());
    }
;

string returns [String s]
    : t=StringLit {
        s = ParameterFactory.unquote(t.getText());
    }
;

name returns [String s]
    : t=lname {
        s = t;
    }
    | t=uname {
        s = t;
    }
;

uname returns [String s]
    : n=Uname {
        s = n.getText();
    }
    | t=(Repeat | RepeatS | Timer | WallTimer | Delay | AnyDelay | AnyK) {
        s = t.getText();
    }
;

lname returns [String s]
    : n=Lname {
        s = n.getText();
    }
    | t=( LC_defaults | LC_let | LC_declare | LC_import ) {
        s = t.getText();
    }
;
