/*   Type:        ANTLR
 *   Title:       PTRS grammar
 *   Description: A grammar definiton for PTRS programs based on the grammar for TRS
 *   Project:     AProVE
 *   Authors:     Jan-Christoph Kassing
 *   Copyright:   Copyright (c) 2022
 *   Department:  RWTH Aachen / Templergraben 55 / D-52056 Aachen
 */

grammar newPtrs;

options {
    language = Java;
}

// replace default error recovery behavior for parser by actually /rejecting/
// unsupported inputs instead of recovering using the follow set
// (alternative fix: override reportError methods as in Strategy.g)
@rulecatch {
catch (RecognitionException e) {
    if (true) {
        // if (true): kludge to persuade the Java compiler that some later
        // (here auto-generated) unreachable return statements might be
        // reachable after all and is thus not to be deemed a compile error
        throw e;
    }
}
}

@header {
package aprove.input.Generated.newPtrs;

import org.apache.commons.math3.fraction.BigFraction;

import aprove.input.Utility.RawPtrs;
import aprove.input.Utility.UnhandledConstructException;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;
import aprove.verification.probabilistic.BasicStructures.*;

import java.util.Set;
import java.util.Map;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;

}

@lexer::header {
package aprove.input.Generated.newPtrs;
}

trs returns [RawPtrs rawptrs = new RawPtrs()]
    : ('(' decl[rawptrs] ')')*
;

decl[RawPtrs rawptrs]
    : VAR ids=idlist {
        for (String v : ids)
            rawptrs.addVariable(TRSTerm.createVariable(v));
    }
    | RULES rules=listofrules[rawptrs, false] {
        rawptrs.hasRules();
    }
    | STRATEGY strategydecl[rawptrs]
    | STARTTERM starttermdecl[rawptrs]
    | GOAL goaldecl[rawptrs]
    | IDENTIFIER commentOrIgn
;

goaldecl [RawPtrs rawptrs]
    : AST { rawptrs.setAst(true); }
    | PAST { rawptrs.setPast(true); }
    | SAST { rawptrs.setSast(true); }
    | TERMINATION { rawptrs.setTermination(true); }
    | COMPLEXITY { rawptrs.setComplexity(true); }
;

strategydecl [RawPtrs rawptrs]
    : INNERMOST { rawptrs.setInnermost(); }
    | OUTERMOST { rawptrs.setOutermost(); }
;

starttermdecl [RawPtrs rawptrs]
    : BASIC { rawptrs.setBasic(true); }
    | ALL { rawptrs.setBasic(false); }
;

// properly nested comments or stuff we don't know. we must parse this :-(
commentOrIgn    : ignored*;
ignored         : identifier
                | STRING
                | ','
                | '->'
                | '->='
                | '-><-'
                | '=='
                | '|'
                | '||'
                | '/'
                | '(' commentOrIgn ')';

listofrules[RawPtrs rawptrs, boolean pairs]
    : (condRule[rawptrs, pairs]) *
;

condRule[RawPtrs rawptrs, boolean pairs]
    : lhs=term[rawptrs] relative=arrow rhs=ruleRhs[rawptrs] {
	    rawptrs.addProbabilisticRule(lhs, rhs);
    }
;

arrow returns [Boolean b]
    : '->' { b = false; }
;

ruleRhs[RawPtrs rawptrs] returns [MultiDistribution<TRSTerm> r]
    : rhsDist=termdistributionOne[rawptrs] {
             r = rhsDist;
    }
    | rhsDist=termdistributionTwo[rawptrs] {
             r = rhsDist;
    }
;

listofterms[RawPtrs rawptrs] returns [Set<TRSTerm> terms]
    @init {
        terms = new LinkedHashSet<TRSTerm> ();
    }
    : (t = term[rawptrs] { terms.add(t); }) *
;

term[RawPtrs rawptrs] returns [TRSTerm t]
    : id=identifier ('(' tl=termlist[rawptrs] ')')? {
        if (rawptrs.isVariable(id)) {
            return TRSTerm.createVariable(id);
        } else {
            if (tl == null) {
                tl = TRSTerm.EMPTY_ARGS;
            }
            FunctionSymbol f = FunctionSymbol.create(id, tl.size());
            return TRSTerm.createFunctionApplication(f, tl);
        }
    }
;

termlist[RawPtrs rawptrs] returns [ArrayList<TRSTerm> terms]
    @init {
        terms = new ArrayList<TRSTerm>();
    }
    :
    | t=term[rawptrs] { terms.add(t); }
      (','
            t=term[rawptrs] { terms.add(t); }
      )*
;

termdistributionOne[RawPtrs rawptrs] returns [MultiDistribution<TRSTerm> termdist]
    @init {
        MultiDistribution.Builder<TRSTerm> distBuilder = new MultiDistribution.Builder<>();
    }
    @after {
        termdist = distBuilder.build();
    }
    : p=INTEGER ':' t=term[rawptrs] { distBuilder.add(t, Integer.parseInt(p.getText())); }
      ('||'
            p=INTEGER ':' t=term[rawptrs] { distBuilder.add(t, Integer.parseInt(p.getText())); }
      )*
;

termdistributionTwo[RawPtrs rawptrs] returns [MultiDistribution<TRSTerm> termdist]
    @init {
        MultiDistribution.Builder<TRSTerm> distBuilder = new MultiDistribution.Builder<>();
    }
    @after {
        termdist = distBuilder.build();
    }
    : p=decimal ':' t=term[rawptrs] { distBuilder.add(t, p); }
      ('||'
            p=decimal ':' t=term[rawptrs] { distBuilder.add(t, p); }
      )*
    
;


decimal returns [BigFraction d]
    : a=INTEGER '/' b=INTEGER { d = new BigFraction(Integer.parseInt(a.getText()),Integer.parseInt(b.getText())); }
;

idlist returns [ArrayList<String> idlist = new ArrayList<String>()]
    : (id=identifier { idlist.add(id); })*
;

integer returns [int i]
    : intstring=INTEGER { i = Integer.parseInt(intstring.getText()); };

identifier returns [String s]
    : kw=keyword { s = kw; }
    | number=INTEGER { s = number.getText(); }
    | id=IDENTIFIER { s = id.getText(); }
;

keyword returns [String kw]
    : tok=(AST | PAST | SAST | TERMINATION | GOAL | INNERMOST | OUTERMOST | NOT | RULES | STRATEGY | VAR | STARTTERM | ALL | BASIC)
    { kw = tok.getText(); }
;

/* this allows language words to be used as identifiers */
/* see http://www.antlr.org/wiki/pages/viewpage.action?pageId=1741 */
/* if you update this list, also update the keyword rule above */
AST              		: 'AST';
PAST        			: 'PAST';
SAST        			: 'SAST';
TERMINATION             : 'TERMINATION';
COMPLEXITY            	: 'COMPLEXITY';
INNERMOST               : 'INNERMOST';
OUTERMOST               : 'OUTERMOST';
GOAL                    : 'GOAL';
NOT                     : 'NOT';
RULES                   : 'RULES';
STRATEGY                : 'STRATEGY';
VAR                     : 'VAR';
STARTTERM               : 'STARTTERM';
ALL                     : 'ALL';
BASIC                   : 'BASIC';

STRING
    : '"' s=(Nondq*) '"'
;
INTEGER
    : s=('0'..'9')+
;
IDENTIFIER
    : IDENTCHAR+
;

fragment IDENTCHAR         : ~(' '| '(' | ')' | '"' | '|' | ','| '\t' | '\r' | '\n' | '/');
fragment Nondq          : ~('"');

WHITESPACE : ( '\t' | ' ' | '\r' | '\n')+ { $channel = HIDDEN; };

