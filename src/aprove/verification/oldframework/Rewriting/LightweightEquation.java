package aprove.verification.oldframework.Rewriting ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 *  A lightweight Equation between two terms without any functionality,
 *  but with a different form of equality. Equastions are considered equal if
 *  they are variable renamings of each other, i.e.
 *  <code>f(x,y) == y</code> and <code>x == f(y, x)</code> are equal w.r.t.
 *  this definition.
 *  @author Stephan Falke
 *  @version $Id$
 */

public class LightweightEquation {

    protected AlgebraTerm s, t;
    private AlgebraTerm transS1, transT1;
    private AlgebraTerm transS2, transT2;
    private Set<AlgebraTerm> transSs, transTs;
    private int hashCode;
    protected String str;

    /* constructors */

    protected LightweightEquation(AlgebraTerm s, AlgebraTerm t) {
    this.s = s;
    this.t = t;

    Vector<AlgebraVariable> varsST = this.getVarsST();
    VarRenaming sigmaST = (VarRenaming)VarRenaming.create();
    int n = varsST.size();
    for(int i=0; i<n; i++) {
        AlgebraVariable v = varsST.elementAt(i);
        VariableSymbol vSymb = v.getVariableSymbol();
        Sort vSort = vSymb.getSort();
        sigmaST.putVar(vSymb, AlgebraVariable.create(VariableSymbol.create("x_"+i, vSort)));
    }
    this.transS1 = s.apply(sigmaST);
    this.transT1 = t.apply(sigmaST);
        boolean same1 = (this.transS1.hashCode() == this.transT1.hashCode());

    Vector<AlgebraVariable> varsTS = this.getVarsTS();
    VarRenaming sigmaTS = (VarRenaming)VarRenaming.create();
    int m = varsST.size();
    for(int i=0; i<m; i++) {
        AlgebraVariable v = varsTS.elementAt(i);
        VariableSymbol vSymb = v.getVariableSymbol();
        Sort vSort = vSymb.getSort();
        sigmaTS.putVar(vSymb, AlgebraVariable.create(VariableSymbol.create("x_"+i, vSort)));
    }
    this.transS2 = s.apply(sigmaTS);
    this.transT2 = t.apply(sigmaTS);
        boolean same2 = (this.transS1.hashCode() == this.transT1.hashCode());

        this.transSs = new HashSet<AlgebraTerm>();
        this.transTs = new HashSet<AlgebraTerm>();
        this.transSs.add(this.transS1);
        this.transSs.add(this.transS2);
        if (same1) {
            this.transSs.add(this.transT1);
        }
        if (same2) {
            this.transSs.add(this.transT2);
        }
        this.transTs.add(this.transT1);
        this.transTs.add(this.transT2);
        if (same1) {
            this.transTs.add(this.transS1);
        }
        if (same2) {
            this.transTs.add(this.transS2);
        }

    this.str = s.toString() + " == " + t.toString();
    this.hashCode = Math.min(this.transSs.hashCode(), this.transTs.hashCode());
    }

    protected LightweightEquation(LightweightEquation e) {
    this.s = e.s.deepcopy();
    this.t = e.t.deepcopy();
    this.transS1 = e.transS1.deepcopy();
    this.transT1 = e.transT1.deepcopy();
    this.transS2 = e.transS2.deepcopy();
    this.transT2 = e.transT2.deepcopy();
    this.hashCode = e.hashCode;
    this.str = e.str;
        this.transSs = new HashSet<AlgebraTerm>(e.transSs);
        this.transTs = new HashSet<AlgebraTerm>(e.transTs);
    }


    /** Constructor for a lightweight equation.
     */
    public static LightweightEquation create(AlgebraTerm left, AlgebraTerm right) {
    return new LightweightEquation(left, right);
    }

    /** Constructor for a lightweight equation.
     */
    public static LightweightEquation create(Rule r) {
    return new LightweightEquation(r.getLeft(), r.getRight());
    }

    /** Constructor for a lightweight equation.
     */
    public static LightweightEquation create(TRSEquation e) {
    return new LightweightEquation(e.getOneSide(), e.getOtherSide());
    }

    private static LightweightEquation create(LightweightEquation e) {
    return new LightweightEquation(e);
    }

    /** Returns one side of this equation.
     */
    public AlgebraTerm getOneSide() {
    return this.s;
    }

    /** Returns the other side of this equation.
     */
    public AlgebraTerm getOtherSide() {
        return this.t;
    }

    /** Determines whether is equation is trivial, i.e. whether its sides
     * are syntactically equal.
     */
    public boolean isTrivial() {
    return this.s.equals(this.t);
    }

    /** Returns a new equation where both sides of the equation are normal forms
     * w.r.t. <code>R</code> of this sides of this rule.
     */
    public LightweightEquation normalize(LightweightRules R) {
    Collection<Rule> rules = R.toRules();
    return LightweightEquation.create(this.s.normalize(rules), this.t.normalize(rules));
    }

    @Override
    public boolean equals(Object o) {
    LightweightEquation e;
    try {
        e = (LightweightEquation)o;
    }
    catch(ClassCastException exc) {
        return false;
    }
    return this.transSs.equals(e.transSs) &&
           this.transTs.equals(e.transTs);
    }

    @Override
    public int hashCode() {
    return this.hashCode;
    }

    public LightweightEquation deepcopy() {
    return LightweightEquation.create(this);
    }

    /** Return a string representation of this rule.
     */
    @Override
    public String toString() {
    return this.str;
    }

    private void merge(Vector<AlgebraVariable> l, Vector<AlgebraVariable> r) {
    Iterator i = r.iterator();
    while(i.hasNext()) {
        AlgebraVariable v = (AlgebraVariable)i.next();
        if(!l.contains(v)) {
        l.add(v);
        }
    }
    return;
    }

    private Vector<AlgebraVariable> getVarsST() {
    Vector<AlgebraVariable> res = this.getVars(this.s);
    this.merge(res, this.getVars(this.t));
    return res;
    }

    private Vector<AlgebraVariable> getVarsTS() {
    Vector<AlgebraVariable> res = this.getVars(this.t);
    this.merge(res, this.getVars(this.s));
    return res;
    }

    private Vector<AlgebraVariable> getVars(AlgebraTerm t) {
    Vector<AlgebraVariable> res = new Vector<AlgebraVariable>();
    if(t.isVariable()) {
        res.add((AlgebraVariable) t);
    }
    else {
        Iterator i = t.getArguments().iterator();
        while(i.hasNext()) {
        this.merge(res, this.getVars((AlgebraTerm)i.next()));
        }
    }
    return res;
    }

}
