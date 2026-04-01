package aprove.input.Programs.ipad;

import java.util.*;

import aprove.input.Generated.ipad.node.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** Treewalker that collects the witness-term of every sort.
 *  @version $Id$
 *  @author Christian Haselbach
 */

class WitnessPass extends Pass {

    private Stack<AlgebraTerm> terms;
    private Stack<Sort> sorts;

    @Override
    public void inStart(Start node) {
    this.terms = new Stack<AlgebraTerm>();
    this.sorts = new Stack<Sort>();
    }

    @Override
    public void outStart(Start node) {
    Iterator it = this.witnessTerms.entrySet().iterator();
    while (it.hasNext()) {
        Map.Entry e = (Map.Entry)it.next();
        Sort s = this.prog.getSort((String)e.getKey());
        s.setWitnessTerm((AlgebraTerm)e.getValue());
    }
    }

    @Override
    public void caseAStruct(AStruct node) {
    TId id = node.getStructname();
    String name = this.chop(id);
        TypeDefinition td = this.typeContext.getTypeDef(name);
    PWitnessterm witnessterm = node.getWitnessterm();
    if (witnessterm != null) {
        Sort s = this.prog.getSort(name);
        this.sorts.push(s);
        witnessterm.apply(this);
        AlgebraTerm witnessTerm = (AlgebraTerm) this.terms.pop();
        this.witnessTerms.put(name, witnessTerm);
        td.setWitnessTerm(witnessTerm);
    }
    }

    @Override
    public void caseAFunctAppSterm(AFunctAppSterm node) {
    TId id = node.getId();
    String name = this.chop(id);
    Sort s = (Sort)this.sorts.pop();
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
    if (f == null) {
        this.addParseError(id, "unknown function-symbol");
        this.pushdummyterm(s);
        return;
    }
    if (f instanceof DefFunctionSymbol) {
        this.addParseError(id, "witness-terms must be constructor-ground-terms");
    }
    if (!this.checksorts(s, f.getSort(), id)) {
        this.addParseError(id, "''"+id+"'' has got sort ''"+f.getSort().getName()+
            "'', but ''"+s.getName()+"'' expected.");
        this.pushdummyterm(s);
        return;
    }
    PTermlist termlist = node.getTermlist();
    for (int i=f.getArity()-1; i>=0; i--) {this.sorts.push(f.getArgSort(i));}
    int size = ((ATermlist)termlist).getCommaterm().size()+1;
    if (f.getArity() != size) {
        this.addParseError(id,
            "expected "+ Integer.valueOf(f.getArity()).toString()+
            " parameters, not "+ Integer.valueOf(size).toString());
        this.pushdummyterm(s);
        return;
    }
    termlist.apply(this);
    this.addArguments(f, size);
    }

    @Override
    public void caseAConstVarSterm(AConstVarSterm node) {
    TId id = node.getId();
    String name = this.chop(id);
    Symbol sym = this.prog.getSymbol(name);
    Sort s = (Sort)this.sorts.pop();
    if (sym == null) {  // not a function or constructor
        this.addParseError(id, "unknown symbol");
        this.pushdummyterm(s);
    }
    else {
        if (((SyntacticFunctionSymbol)sym).getArity() != 0) {
        this.addParseError(id, "missing parameter list for function or constructor ''"+name+"''");
        }
        if (!this.checksorts(s, sym.getSort(), id)) {
        this.addParseError(id,
                "function or constructor ''"+this.chop(id)+
                "'' has got sort '"+sym.getSort()+
                "'' but ''"+s+"'' expected.");
        this.pushdummyterm(s);
        return;
        }
        this.terms.add(AlgebraFunctionApplication.create((SyntacticFunctionSymbol)sym));
    }
    }

    @Override
    public void caseATermlist(ATermlist node) {
    node.getTerm().apply(this);
    LinkedList tcs = node.getCommaterm();
    Iterator it = tcs.iterator();
    while (it.hasNext()) {
        ((ACommaterm)it.next()).getTerm().apply(this);
    }
    }

    @Override
    public void caseACommaterm(ACommaterm node) {
    node.getTerm().apply(this);
    }

    private void addArguments(SyntacticFunctionSymbol f, int n) {
    Vector<AlgebraTerm> t = new Vector<AlgebraTerm>();
    try {
        for (int i=0; i<n; i++) {t.insertElementAt((AlgebraTerm)this.terms.pop(), 0);}
    } catch (EmptyStackException e) {
        return;
    }
    if (f instanceof DefFunctionSymbol) {
        this.terms.add(DefFunctionApp.create((DefFunctionSymbol)f, t));
    } else {
        this.terms.add(ConstructorApp.create((ConstructorSymbol)f, t));
    }
    }

    // We do not want to visit anything else in this pass.
    @Override
    public void caseAFunct(AFunct node) {}

    protected void pushdummyterm(Sort s) {
    ConstructorSymbol dummyconst = ConstructorSymbol.create(s.getName()+"dummy", new Vector<Sort>(), s);
    AlgebraTerm t = ConstructorApp.create(dummyconst);
    this.terms.add(t);
    }

}
