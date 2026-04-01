package aprove.input.Terms.term;

import java.util.*;

import aprove.input.Generated.term.node.*;
import aprove.input.Generated.term.parser.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that converts an abstract syntax tree to the internal term representation.
 * @author Peter Schneider-Kamp, Christian Haselbach
 * @version $Id$
 */

class Pass1 extends Pass {

    @Override
    public void outStart(Start node) {
    this.term = this.terms.pop();
    }

    @Override
    public void inAVarNterm(AVarNterm node) {
    Token id = node.getVarId();
    String name = this.chop(id);
    Symbol sym = this.prog.getSymbol(name);
    Sort s = (Sort)this.sorts.pop();
    if (this.prog.getSort(name) != null) {
        this.errors.add(new ParserException(id,"cannot use sort symbol '"+name+"' in term"));
    }
    sym = (Symbol)this.gvars.get(name);
    if (sym == null) {
        sym = VariableSymbol.create(name,s);
    }
    else {
        this.checksorts(sym, s, id);
    }
    this.terms.add(AlgebraVariable.create((VariableSymbol)sym));
    }

    @Override
    public void inAConstNterm(AConstNterm node) {
    Token id = node.getPrefixId();
    String name = this.chop(id);
    Symbol sym = this.prog.getSymbol(name);
        Sort s = (Sort)this.sorts.pop();
        SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)sym;
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        if (f.getArity() != 0) {
            this.errors.add(new ParserException(id, "missing parameter list for function or constructor '"+name+"'"));
            // BEGIN "ugly hack"
            AlgebraTerm u = AlgebraVariable.create(VariableSymbol.create("undefined", this.poly));
            for (int i=0; i<f.getArity(); i++) {args.add(u);}
            // END "ugly hack"
        }
        this.checksorts(sym, s, id);
        this.terms.add(AlgebraFunctionApplication.create(f, args));
}

    @Override
    public void caseAFunctAppNterm(AFunctAppNterm node) {
    Token id = node.getPrefixId();
    int size = ((ATermlist)node.getTermlist()).getTermcomma().size()+1;
    String name = this.chop(id);
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        if (f == null) {
            f = this.prog.getPredefFunctionSymbol(name);
            if (f != null) {
                try {
                    this.prog.activatePredefFunctionSymbol(name);
                } catch (ProgramException e) {
                    this.errors.add(new ParserException(id,"'"+name+"' already declared in program"));
                    for (int i=0; i<size; i++) {this.sorts.push(this.poly);}
                }
            }
        }
        if (f == null) {
            this.errors.add(new ParserException(id,"undeclared function or constructor '"+name+"'"));
            for (int i=0; i<size; i++) {this.sorts.push(this.poly);}
    }
    else {
        Sort s = (Sort)this.sorts.pop();
        this.checksorts(f, s, id);
        for (int i=f.getArity()-1; i>=0; i--) {this.sorts.push(f.getArgSort(i));}
        if (f.getArity() != size) {
        this.errors.add(new ParserException(id, "expected "+Integer.valueOf(f.getArity()).toString()+" parameters, not "+Integer.valueOf(size).toString()));
        // BEGIN "ugly hack"
        AlgebraTerm u = AlgebraVariable.create(VariableSymbol.create("undefined", this.poly));
        for (int i=0; i<f.getArity()-size; i++) {this.terms.add(u);}
        for (int i=0; i<size-f.getArity(); i++) {this.sorts.push(f.getSort());}
        // END "ugly hack"
        }
    }
    node.getTermlist().apply(this);
    if (f == null) {
        AlgebraTerm t = AlgebraVariable.create(VariableSymbol.create("undefined", this.poly));
        for (int i=0; i<size; i++) {this.terms.pop();}
        this.terms.add(t);
    } else {
        size = f.getArity();
        Vector<AlgebraTerm> t = new Vector<AlgebraTerm>();
        for (int i=0; i<size; i++) {t.insertElementAt(this.terms.pop(), 0);}
        this.terms.add(AlgebraFunctionApplication.create(f, t));
    }
    }

    @Override
    public void caseAInfixTerm(AInfixTerm node) {
    Token id = node.getInfixId();
    String name = this.chop(id);
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        if (f == null) {
            f = this.prog.getPredefFunctionSymbol(name);
            if (f != null) {
                try {
                    this.prog.activatePredefFunctionSymbol(name);
                } catch (ProgramException e) {
                    this.errors.add(new ParserException(id,"'"+name+"' already declared in program"));
                    for (int i=0; i<2; i++) {this.sorts.push(this.poly);}
                }
            }
        }
        if (f == null) {
            this.errors.add(new ParserException(id,"undeclared function or constructor '"+name+"'"));
            for (int i=0; i<2; i++) {this.sorts.push(this.poly);}
    }
    else {
        List<AlgebraTerm> ts = new Vector<AlgebraTerm>();
        this.sorts.push(f.getArgSort(0));
        node.getLeft().apply(this);
        ts.add(this.terms.pop());
        this.sorts.push(f.getArgSort(1));
        node.getRight().apply(this);
        ts.add(this.terms.pop());
        this.terms.add(AlgebraFunctionApplication.create((SyntacticFunctionSymbol)f, ts));
    }
    }
}

