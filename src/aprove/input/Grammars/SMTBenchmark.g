/*   Type:        ANTLR
 *   Title:       SMT-LIB 2.0 grammar for Benchmarks
 *   Description: A grammar definiton for SMT-LIB programs
 *   Project:     AProVE
 *   Authors:     Andrej Dyck
 *   Copyright:   Copyright (c) 2010
 *   Department:  RWTH Aachen / Templergraben 55 / D-52056 Aachen
 */
 
grammar SMTBenchmark;

options {
	language = Java;
}

@header {
package aprove.input.Generated.SMTLIB;

import aprove.input.Programs.SMTLIB.*;
import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.input.Programs.SMTLIB.Namespaces.*;
import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

import java.math.*;
import java.util.*;

import org.antlr.runtime.BitSet;
}

@lexer::header {
package aprove.input.Generated.SMTLIB;
}

/*------------------------------------------------------------------
 * PARSER RULES
 *------------------------------------------------------------------*/
 
/* THE THREE MAIN COMPONENTS OF THE SMT_LIB LANGUAGE */
/* ------------------------------------------------- */
/* 1. THEORIES */
theory_decl //returns [SMTTheory script = new SMTTheory()]
	:	'(' 'theory' SYMBOL theory_attribute+ ')'
	;
	
/* 2. LOGICS */
logic //returns [SMTLogic script = new SMTLogic()]
	:	'(' 'logic' SYMBOL logic_attribute+ ')'
	;
	
/* 3. SCRIPTS */
script returns [SMTBenchmark script = SMTBenchmark.create()]
	:	command[script]*
	;
/* ------------------------------------------------- */

/* S-expressions */
spec_constant returns [BigInteger n]
	:	NUMERAL { String s = $NUMERAL.text;
	            n = new BigInteger(s); }
	|	DECIMAL {}
	| HEXADECIMAL {}
	| BINARY {}
	| STRING {}
	;

s_expr
	:	spec_constant|SYMBOL|KEYWORD|'(' s_expr* ')'
	;
	
/* identifiers */
identifier returns [String s]
	: SYMBOL { s = $SYMBOL.text; }
	|'(' '_' SYMBOL NUMERAL+ ')' { s = $SYMBOL.text + "_" + $NUMERAL.text; }
	;
	
/* Sorts */
sort returns [AbstractSort sort]
	:	'Bool' { sort = SortBool.SORTBOOL; }
	| 'Int' { sort = SortInt.SORTINT; }
	| identifier { if(true) {throw new UnsupportedException("Other sorts except 'Bool' and 'Int' are not supported.");} }
	| '(' identifier sort+ ')' { if(true) {throw new UnsupportedException("Other sorts except 'Bool' and 'Int' are not supported.");} }
	;
	
/* Attributes */
attribute_value
	:	spec_constant|SYMBOL|'(' s_expr* ')'
	;

attribute
	:	KEYWORD attribute_value?
	;
	
/* Terms */
qual_identifier returns [String s]
	:	id=identifier { s = id; }
	| '(' 'as' identifier sort ')' { if(true) {throw new UnsupportedException("'as'-identifier are not supported.");} }
	;

var_binding[SMTTermFactory factory] returns [Pair<String, SMTTermWrapper> p]
	:	'(' SYMBOL t=term[factory] ')'
	  { p = new Pair<String, SMTTermWrapper>($SYMBOL.text, t); } 
	;
	
var_bindings[SMTTermFactory factory] returns [SMTTermFactory newfactory = new SMTTermFactory(factory)]
  : (p=var_binding[factory]{ newfactory.addBinding(p.getKey(), p.getValue()); })+
  ;
	
sorted_var
	:	'(' SYMBOL sort ')'
	;
	
terms[SMTTermFactory factory] returns [List<SMTTermWrapper> terms = new LinkedList<SMTTermWrapper>()]
	: (t=term[factory]{ terms.add(t); })+
	;
	
term[SMTTermFactory factory] returns [SMTTermWrapper term]
	:	c=spec_constant
	  { term = factory.create(c); }
	| id=qual_identifier
	  { term = factory.create(id); }
	| '(' id=qual_identifier ts=terms[factory] ')'
	  { term = factory.create(id, ts); }
	| '(' 'distinct' t=term[factory] ts=terms[factory] ')'
	  { if(true) {throw new UnsupportedException("term : distinct is not supported.");} }
	| '(' 'let' '(' newfactory=var_bindings[factory] ')' t=term[newfactory] ')'
	  { newfactory.putConstraintsIntoTerm(t);
	    term = t; }
	| '(' 'forall' '(' sorted_var+ ')' t=term[factory] ')'
	  { if(true) {throw new UnsupportedException("term : forall is not supported.");} }
	| '(' 'exists' '(' sorted_var+ ')' term[factory] ')'
	  { if(true) {throw new UnsupportedException("term : exists is not supported.");} }
	| '(' '!' term[factory] attribute+ ')'
	  { if(true) {throw new UnsupportedException("term : ! is not supported.");} }
	;
	
/* Theories (FOR 1. THEORIES) */
sort_symbol_decl
	:	'(' identifier NUMERAL attribute* ')'
	;
	
meta_spec_constant
	:	'NUMERAL'|'DECIMAL'|'STRING'
	;

fun_symbol_decl
	: '(' spec_constant sort attribute* ')'
	| '(' meta_spec_constant sort attribute* ')'
	| '(' identifier sort+ attribute* ')'
	;
	
par_fun_symbol_decl
	:	fun_symbol_decl
	| '(' 'par' '(' SYMBOL+ ')' '(' identifier sort+ attribute* ')' ')'
	;
	
theory_attribute
	:	':sorts' '(' sort_symbol_decl+ ')'
	| ':funs' '(' par_fun_symbol_decl+ ')'
	| ':sorts-description' STRING
	| ':funs-description' STRING
	| ':definition' STRING
	| ':values' STRING
	| ':notes' STRING
	| attribute
	;
	
/* Logics (FOR 2. LOGICS) */
logic_attribute
	:	':theories' '(' SYMBOL+ ')'
	| ':language' STRING
	| ':extensions' STRING
	| ':values' STRING
	| ':notes' STRING
	| attribute
	;
	
/* Command options (FOR 3. SCRIPTS) */
/*b_value
	:	'true' | 'false'
	;
	
option
	:	':print-success' b_value
	| ':expand-definitions' b_value
	| ':interactive-mode' b_value
	| ':produce-proofs' b_value
	| ':produce-unsat-cores' b_value
	| ':produce-models' b_value
	| ':produce-assignments' b_value
	| ':regular-output-channel' STRING
	| ':diagnostic-output-channel' STRING
	| ':random-seed' NUMERAL
	| ':verbosity' NUMERAL
	| attribute
	;*/
	
/* Info flags */
info_flag
	:	':error-behavior'
	| ':name'
	| ':authors'
	| ':version'
	| ':status'
	|	':reason-unknown'
	| ':all-statistics'
	| KEYWORD
	;
	
/* Commands */

/* assertion-set stermtack: the single global stack of sets.
 * assertion sets: the sets whi.gch are the elements on the stack.
 * set of all assertions: the union of all the assertion sets currently on the assertion-set stack.
 * current assertion set: the assertion set (if any) currently on the top of the stack.
 */
command[SMTBenchmark script]
	: '(' 'set-logic' SYMBOL ')'
	  { script.setLogic($SYMBOL.text); }
	//| '(' 'set-option' option ')'
	| '(' 'set-info' info_flag attribute_value? ')'
	  { script.setInfo($info_flag.text, $attribute_value.text); }
	| '(' 'declare-sort' SYMBOL NUMERAL ')'
	  { if(true) {throw new UnsupportedException("Command 'declare-sort' is not supported.");} }
	| '(' 'define-sort' SYMBOL '(' SYMBOL* ')' sort ')'
	  { if(true) {throw new UnsupportedException("Command 'define-sort' is not supported.");} }
	| '(' 'declare-fun' SYMBOL '(' sort* ')' to=sort ')'
	  { script.declareFun($SYMBOL.text, (NativeSort)to); }
	| '(' 'define-fun' SYMBOL '(' sorted_var* ')' sort term[new SMTTermFactory(script)] ')'
	  { if(true) {throw new UnsupportedException("Command 'define-fun' is not supported.");} }
	//| '(' 'push' NUMERAL ')'
	//| '(' 'pop' NUMERAL ')'
	| '(' 'assert' t=term[new SMTTermFactory(script)] ')'
	  { script.assertFormula(t.getDiophantineFormula());
	    script.assertFormula(t.getConstraints()); }
	| '(' 'check-sat' ')'
	  { script.checkSat(); }
	//| '(' 'get-assertions' ')'
	//| '(' 'get-proof' ')'
	//| '(' 'get-unsat-core' ')'
	//| '(' 'get-value' '(' terms[new SMTTermFactory(script.getNamespace())] ')' ')'
	//| '(' 'get-assignment' ')'
	//| '(' 'get-option' KEYWORD ')'
	//| '(' 'get-info' info_flag ')'
	| '(' 'exit' ')'
	  { /* NOOP */ }
	;
	
/*------------------------------------------------------------------
 * LEXER RULES
 *------------------------------------------------------------------*/

WHITESPACE : ( '\t' | ' ' | '\r' | '\n'| '\u000C' )+ 	{ $channel = HIDDEN; } ;

COMMENT :	';'~('\n'|'\r')*'\r'?'\n' {$channel=HIDDEN;} ;

NUMERAL 
	:	'0'|'1'..'9'(DIGIT)*
	;
	
DECIMAL
	:	NUMERAL'.''0'*NUMERAL
	;
	
HEXADECIMAL
	:	'#x'HEX_DIGIT+
	;
	
BINARY
	:	'#b'('0'|'1')+
	;
	
STRING
    :  '"' ( ~('\\'|'"') | EscapeSequence )* '"'
    ;
    
SYMBOL
	:	(LETTER|PREDSYMBOL)(LETTER|PREDSYMBOL|DIGIT)*
	//| '|'PRINTABLECHAR*'|'
	| '|'~('|')*'|'
	;
	
KEYWORD
	:	':'(LETTER|PREDSYMBOL|DIGIT)+
	;
	
/*------------------------------------------------------------------
 * FRAGMENTS
 *------------------------------------------------------------------*/

fragment
PREDSYMBOL :	'+' | '-' | '/' | '*' | '=' | '%' | '?' | '!' | '.' | '$' | '_' | '~' | '&' | '^' | '<' | '>' | '@' ;

fragment
LETTER : 'a'..'z'|'A'..'Z' ;

fragment
HEX_DIGIT : DIGIT | 'a'..'f' | 'A'..'F' ;

fragment
DIGIT :	 '0'..'9' ;

fragment
PRINTABLECHAR : ' '..'~' ; /* printable characters in ASCII */

fragment
EscapeSequence
    :   '\\' ('b'|'t'|'n'|'f'|'r'|'\"'|'\''|'\\')
    |   OctalEscape
    ;

fragment
OctalEscape
    :   '\\' ('0'..'3') ('0'..'7') ('0'..'7')
    |   '\\' ('0'..'7') ('0'..'7')
    |   '\\' ('0'..'7')
    ;