/*   Type:        ANTLR
 *   Title:       TRS/QDP/QCSDP grammar
 *   Description: A grammar definiton for TRS programs
 *   Project:     AProVE
 *   Authors:     Fabian Emmes
 *   Copyright:   Copyright (c) 2009
 *   Department:  RWTH Aachen / Templergraben 55 / D-52056 Aachen
 */

grammar NewIDP;

options {
    language = Java;
}

@header {
package aprove.input.Generated.newIDP;

import aprove.input.Utility.*;
import aprove.input.Utility.RawIDP.IllegalEdgeException;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.IQTermSet.PredefinedQMode;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Polynomials.*;

import immutables.*;

import java.util.Set;
import java.util.Map;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;

}

@lexer::header { 
package aprove.input.Generated.newIDP;
}

itrs returns [RawIDP rawIDP = new RawIDP()]
    : newlinesAndComment
    LEFTPAREN VAR varDecl[rawIDP] RIGHTPAREN
    newlinesAndComment
    (LEFTPAREN PREDEFINED newlines predefinedDecl[rawIDP] RIGHTPAREN newlinesAndComment)?
    ((LEFTPAREN RULES newlines rulesDecl[rawIDP] RIGHTPAREN newlinesAndComment)
    	| (LEFTPAREN TERMS newlines nodesDecl[rawIDP] RIGHTPAREN newlinesAndComment 
     	  (LEFTPAREN EDGES newlines edgesDecl[rawIDP] RIGHTPAREN newlinesAndComment)?
     	  (LEFTPAREN INITIALNODES newlines initialNodesDecl[rawIDP] RIGHTPAREN newlinesAndComment)?))
    (LEFTPAREN STRATEGY newlines strategyDecl[rawIDP] RIGHTPAREN newlinesAndComment)?
    (LEFTPAREN MINIMAL {
        rawIDP.setMinimal(true);
    }
    | NOT MINIMAL {
        rawIDP.setMinimal(false); 
    }RIGHTPAREN)?
;

newlinesAndComment 
	: newlines (commentDecl newlines)?;

commentDecl
    : LEFTPAREN COMMENT commentOrIgn RIGHTPAREN
;
	
varDecl[RawIDP rawIDP]
    : ids=idlist {
        for (String v : ids)
            rawIDP.addVariable(ITerm.createVariable(v, DomainFactory.UNKNOWN));
    } 
;
	
predefinedDecl[RawIDP rawIDP]
    :
;

rulesDecl[RawIDP rawIDP]
   : (r = iRule[rawIDP] {rawIDP.addRule(r);} nextElement) *
;

nodesDecl[RawIDP rawIDP]
   : (iNode[rawIDP] (nextElement iNode[rawIDP])*)?
;    

edgesDecl[RawIDP rawIDP]
    @init {
    	rawIDP.initEdges();
    }
    : (LEFTPAREN from = integer RIGHTPAREN EDGEAT fromPos = position ARROW '^' t=edgeType LEFTPAREN to = integer RIGHTPAREN ((LEFTBRACK renaming = varRenaming[rawIDP] RIGHTBRACK)? CONDITION conds = itpf[rawIDP])? nextElement {
        try {
            rawIDP.addEdge(from, fromPos, to, t, renaming, conds);
        } catch (IllegalEdgeException e) {
            throw new NoViableAltException (e.getMessage(), -1, -1, this.input);
        }
    })*
;

edgeType returns [EdgeType t] 
    : 'INF' {t = EdgeType.INF;}
    | 'REWRITE' {t = EdgeType.REWRITE;}
    | 'REWRITE_INF' {t = EdgeType.REWRITE_INF;}
;

initialNodesDecl[RawIDP rawIDP]
    : (LEFTPAREN n = integer LEFTPAREN ','? {
      	rawIDP.addInitialNode(n);
    })*
;


strategyDecl[RawIDP rawIDP]
    : (INNERMOST { 
    	rawIDP.createInnermostQ(); })
    | (CONSTRUCTOR { 
    	rawIDP.createConstructorQ(); })
    | (LEFTPAREN Q qDecl[rawIDP] RIGHTPAREN)
;

qDecl[RawIDP rawIDP]
    : qterms = iTermlist[rawIDP] {
        List<IFunctionApplication<?>> fas = new ArrayList<IFunctionApplication<?>>(qterms.size());
        for (ITerm<?> t : qterms) {
            if (t.isVariable()) {
                throw new NoViableAltException ("Variable only terms are not allowed in q.", -1, -1, this.input);
            }
            fas.add((IFunctionApplication<?>)t);
        }
        rawIDP.setQ(new IQTermSet(fas, PredefinedQMode.PredefinedRule, rawIDP.getPredefinedMap()));
    }
;


// $<rules

iRule[RawIDP rawIDP] returns [IRule rule]
    :  lhs=iTerm[rawIDP] ARROW rhs=iTerm[rawIDP] (CONDITION conds=itpf[rawIDP])? {
        if (conds == null) {
            conds = rawIDP.getItpfFactory().createTrue();
        }
        if (lhs.isVariable()) {
            throw new NoViableAltException ("Left hand sides must be function applications.", -1, -1, this.input);
        }
        rule = IRuleFactory.create((IFunctionApplication<?>)lhs, rhs, conds);
    }
;

iNode[RawIDP rawIDP]
    :  t=iTerm[rawIDP] (CONDITION conds=itpf[rawIDP])? {
        if (conds == null) {
            conds = rawIDP.getItpfFactory().createTrue();
        }
        rawIDP.addNode(t, conds);
    }
;

// $>


// $<terms
iTerm[RawIDP rawIDP] returns [ITerm<?> t]
    : b = iBoolExpr[rawIDP] {t = b;}
;

iRealTerm[RawIDP rawIDP] returns [ITerm<?> t]
    : (minu = MINUS (id = number | id = variable))
    {
        ITerm arg;
        if (rawIDP.isVariable(id)) {
            arg = ITerm.createVariable(id, DomainFactory.UNKNOWN);
        } else {
            IFunctionSymbol<?> f = IFunctionSymbol.create(id, 0, 
  	      rawIDP.getPredefinedMap());
            arg = ITerm.createFunctionApplication(f, ITerm.EMPTY_ARGS);
        }
           
        IFunctionSymbol<?> m = IFunctionSymbol.create(minu.getText(), 1, 
	    rawIDP.getPredefinedMap());
        t = ITerm.createFunctionApplication(m, arg);
    }
    | (id=identifier (LEFTPAREN tl=iTermlist[rawIDP] RIGHTPAREN)?)
    {
	if (rawIDP.isVariable(id)) {
		t = ITerm.createVariable(id, DomainFactory.UNKNOWN);
	} else {
		if (tl == null) {
			tl = ITerm.EMPTY_ARGS;
		}
		IFunctionSymbol<?> f = IFunctionSymbol.create(id, tl.size(), 
			rawIDP.getPredefinedMap());
		t = ITerm.createFunctionApplication(f, tl);
	}
	
    }
;

iTermlist[RawIDP rawIDP] returns [ArrayList<ITerm<?>> terms]
    @init {
        terms = new ArrayList<ITerm<?>>();
    }
    : t=iTerm[rawIDP] { terms.add(t); }
      (','
            t=iTerm[rawIDP] { terms.add(t); }
      )*
;


iBoolExpr[RawIDP rawIDP] returns [ITerm<?> t] 
    : l = iBoolTerm[rawIDP] 
    (f = BOR r = iBoolExpr[rawIDP])?
    {
    	if (r != null) {
    	    IFunctionSymbol<?> sym = IFunctionSymbol.create(
    	        f.getText(),
    	        2,
    	  	rawIDP.getPredefinedMap());
    	    t = IFunctionApplication.createFunctionApplication(sym, l, r);
    	} else {
    	    t = l;
    	}
    }
;

iBoolTerm[RawIDP rawIDP] returns [ITerm<?> t] 
    : l = iBoolNot[rawIDP] 
    ( f = BAND r = iBoolTerm[rawIDP] )?
    {
    	if (r != null) {
    	    IFunctionSymbol<?> sym = IFunctionSymbol.create(
    	        f.getText(),
    	        2,
    	  	rawIDP.getPredefinedMap());
    	    t = IFunctionApplication.createFunctionApplication(sym, l, r);
    	} else {
    	    t = l;
    	}
    }
;


iBoolNot[RawIDP rawIDP] returns [ITerm<?> t] 
    : f = BNOT ? r = iRelExpr[rawIDP]
    {
    	if (f != null) {
    	    IFunctionSymbol<?> sym = IFunctionSymbol.create(
    	        f.getText(),
    	        1,
    	  	rawIDP.getPredefinedMap());
    	    t = IFunctionApplication.createFunctionApplication(sym, r);
    	} else {
    	    t = r;
    	}
    }
;

iRelExpr[RawIDP rawIDP] returns [ITerm<?> t] 
    : l = iArithExpr[rawIDP] 
    (f = (GE | GT | LE | LT | EQ) r = iRelExpr[rawIDP])?
    {
    	if (r != null) {
    	    IFunctionSymbol<?> sym = IFunctionSymbol.create(
    	        f.getText(),
    	        2,
    	  	rawIDP.getPredefinedMap());
    	    t = IFunctionApplication.createFunctionApplication(sym, l, r);
    	} else {
    	    t = l;
    	}
    }
;

iArithExpr[RawIDP rawIDP] returns [ITerm<?> t] 
    : l = iArithTerm[rawIDP] 
    (f = (PLUS | MINUS) r = iArithExpr[rawIDP])?
    {
    	if (r != null) {
    	    IFunctionSymbol<?> sym = IFunctionSymbol.create(
    	        f.getText(),
    	        2,
    	  	rawIDP.getPredefinedMap());
    	    t = IFunctionApplication.createFunctionApplication(sym, l, r);
    	} else {
    	    t = l;
    	}
    }
;

iArithTerm[RawIDP rawIDP] returns [ITerm<?> t] 
    : l = iArithFactor[rawIDP] 
    ( f = ( TIMES | DIV | MOD) r = iArithTerm[rawIDP] )?
    {
    	if (r != null) {
    	    IFunctionSymbol<?> sym = IFunctionSymbol.create(
    	        f.getText(),
    	        2,
    	  	rawIDP.getPredefinedMap());
    	    t = IFunctionApplication.createFunctionApplication(sym, l, r);
    	} else {
    	    t = l;
    	}
    }
;
    

iArithFactor[RawIDP rawIDP] returns [ITerm<?> t] 
    : (LEFTPAREN a = iBoolExpr[rawIDP] {t = a;} RIGHTPAREN)
    | b = iRealTerm[rawIDP] {t = b;}
;


// $<itpf
varRenaming[RawIDP rawIDP] returns [VarRenaming res]
    @init {
	Map<IVariable<?>, IVariable<?>> subst = new LinkedHashMap<IVariable<?>, IVariable<?>>();
    }
    : 
    (f = identifier {
    	if (!rawIDP.isVariable(f)) {
            throw new NoViableAltException ("Variable renamings may only contain variable terms.", -1, -1, this.input);
    	}
    }
    '/' t = identifier {
        if (!rawIDP.isVariable(f)) {
            throw new NoViableAltException ("Variable renamings may only contain variable terms.", -1, -1, this.input);
	}
	subst.put(ITerm.createVariable(f, DomainFactory.UNKNOWN), ITerm.createVariable(t, DomainFactory.UNKNOWN));
    })*
    {
     res = VarRenaming.create(ImmutableCreator.create(subst), false, rawIDP.getItpfFactory().getPolyFactory());
    }
;

// $>

itpf[RawIDP rawIDP] returns [Itpf c]
    : conjClauses = itpfConjClauses[rawIDP] 
    { c = rawIDP.getItpfFactory().create(conjClauses); }
;

itpfConjClauses[RawIDP rawIDP] returns [ImmutableSet<ItpfConjClause> clauses]
    @init {
        LinkedHashSet<ItpfConjClause> rawClauses = new LinkedHashSet<ItpfConjClause>();
    }
    :
    c=itpfConjClause[rawIDP]
        { rawClauses.add(c); }
    (ITPFOR
        c=itpfConjClause[rawIDP]
        { rawClauses.add(c); }
    )*
    {
        clauses = ImmutableCreator.create(rawClauses);
    }
;

itpfConjClause[RawIDP rawIDP] returns [ItpfConjClause clause]
    @init {
        LinkedHashMap<ItpfAtom, Boolean> rawLiterals = new LinkedHashMap<ItpfAtom, Boolean>();
    }
    :
    (c=itpfAtom[rawIDP]
            { rawLiterals.put(c, true); } 
    | ITPFNOT c=itpfAtom[rawIDP] 
        {rawLiterals.put(c, false);}
    )
    (ITPFAND
        (c= itpfAtom[rawIDP]
            { rawLiterals.put(c, true); } 
	| ITPFNOT c= itpfAtom[rawIDP] 
            { rawLiterals.put(c, false); } 
	)
    )*
    (LEFTSET
    	s = iTermlist[rawIDP]
    RIGHTSET)?
    {
    	Set<ITerm<?>> S;
    	
    	
    	if (s == null) {
    		S = ITerm.EMPTY_SET;
    	} else {
	    	S = new LinkedHashSet<ITerm<?>>(s);
    	}
        clause = rawIDP.getItpfFactory().createClause(ImmutableCreator.create(rawLiterals), ImmutableCreator.create(S));
    }
;

itpfAtom[RawIDP rawIDP] returns [ItpfAtom atom]
    : a = itpfItp[rawIDP] {atom = a;}
;

itpfItp[RawIDP rawIDP] returns [ItpfItp c]
    : left=iTerm[rawIDP] (rel=itpfItpRelation right=iTerm[rawIDP]?) ?
    { 
        if (rel == null) {
            rel = ItpRelation.TO_TRANS;
        }
        if (right == null) {
            right = rawIDP.getPredefinedMap().getBooleanTrue().getTerm();
        }
        c = rawIDP.getItpfFactory().createItp(left, RelDependency.Increasing, ItpfItp.EMPTY_CONTEXT, rel, right, RelDependency.Increasing, ItpfItp.EMPTY_CONTEXT);
    }
;

itpfItpRelation returns [ItpRelation r] 
    : ARROW {r = ItpRelation.TO;}
    | ITP_TO_TRANS {r = ItpRelation.TO_TRANS;}
    | ITP_TO_PLUS {r = ItpRelation.TO_PLUS;}
    | ITP_EQ {r = ItpRelation.EQ;}
;

// $>
position returns [IPosition p]
    @init {
        ArrayList<Integer> posList = new ArrayList<Integer>();
    }
    : ((i = integer {posList.add(i);}) (',' i = integer {posList.add(i);})*)? {
    	p = IPosition.create(posList);
    } 
;

idlist returns [ArrayList<String> idlist = new ArrayList<String>()]
    : (id=identifier { idlist.add(id); })*
;

integer returns [int i]
    : intstring=INTEGER { i = Integer.parseInt(intstring.getText()); };

identifier returns [String s]
    : kw=keyword { s = kw; }
    | pr=predefinedFunction { s = pr; }
    | num=INTEGER { s = num.getText(); }
    | id=IDENTIFIER { s = id.getText(); }
;

number returns [String s]
    : num=INTEGER { s = num.getText(); }
;

variable returns [String s]
    : id=IDENTIFIER { s = id.getText(); }
;

predefinedFunction returns [String kw]
    : tok=(PLUS | MINUS | DIV | TIMES | MOD | BOR | BAND |  LE | LT | GE | GT | EQ)
    { kw = tok.getText(); }
;

nextElement 
	:	(NEWLINE | ',') NEWLINE*;

keyword returns [String kw]
    : tok=(VAR | PREDEFINED | MINIMAL | NOT
        | STRATEGY | INNERMOST | CONSTRUCTOR | Q | RULES | TERMS | EDGES | INITIALNODES
                | STARTTERM | TERMINATION | COMMENT)
    { kw = tok.getText(); }
;

newlines	: NEWLINE*;

// properly nested comments or stuff we don't know. we must parse this :-(
commentOrIgn    : ignored*;
ignored         : identifier
                | LEFTPAREN commentOrIgn RIGHTPAREN;


/* this allows language words to be used as identifiers */
	/* see http://www.antlr.org/wiki/pages/viewpage.action?pageId=1741 */
VAR                     : 'VAR';
PREDEFINED              : 'PREDEFINED';

MINIMAL                 : 'MINIMAL';
NOT                     : 'NOT';
STRATEGY                : 'STRATEGY';
INNERMOST               : 'INNERMOST';
CONSTRUCTOR             : 'CONSTRUCTOR';
Q                       : 'Q';
RULES                   : 'RULES';
TERMS                   : 'TERMS';
EDGES                   : 'EDGES';
INITIALNODES		: 'INITIAL';
STARTTERM               : 'STARTTERM';
TERMINATION             : 'TERMINATION';
COMMENT                 : 'COMMENT';

RIGHTPAREN              : ')';
LEFTPAREN               : '('; 
RIGHTBRACK              : ']';
LEFTBRACK               : '['; 
LEFTSET                 : '{'; 
RIGHTSET                : '}'; 
CONDITION               : ':|:';
EDGEAT                  : '@';


ARROW 			: '->';
ITP_TO_TRANS		: '->*';
ITP_TO_PLUS		: '->+';
ITP_EQ			: '->=';

// pre-defined functions
PLUS                    : '+'; 
MINUS                   : '-';
DIV                     : '/';
TIMES                   : '*';
MOD                     : '%';
BOR                     : '||';
BAND                    : '&&';
BNOT                    : '!';
ITPFOR                  : '\\||';
ITPFAND                 : '\\&&';
ITPFNOT                 : '\\!';
LE                      : '<=';
LT                      : '<';
GE                      : '>=';
GT                      : '>';
EQ                      : '=';

STRING
    : '"' s=(Nondq*) '"'
;
INTEGER
    : s=('0'..'9')+

;
IDENTIFIER
    : IDENTCHAR+
;

NEWLINE			: '\n';

fragment IDENTCHAR         : ~(' '| LEFTPAREN | RIGHTPAREN | PLUS | MINUS | DIV | TIMES | MOD | BOR | BAND | BNOT | ITPFOR | ITPFAND | LE | LT | GE | GT | EQ | ARROW | '"' | '|' | ','| '\t' | '\r' | NEWLINE);
fragment Nondq          : ~('"');


WHITESPACE : ( '\t' | ' ' | '\r')+ { $channel = HIDDEN; };


