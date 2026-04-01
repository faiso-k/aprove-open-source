package aprove.verification.oldframework.Rewriting ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 *  A lightweight (unconditional) Rule without any functionality, but with
 *  a different form of equality. Rules are considered equal if they are
 *  variable renamings of each other, i.e. <code>f(x,y) -> y</code> and
 *  <code>f(y, x) -> x</code> are equal w.r.t. this definition.
 *  @author Stephan Falke
 *  @version $Id$
 */

public class LightweightRule {

    protected AlgebraTerm left, right;
    private AlgebraTerm transLeft, transRight;
    private int hashCode;
    private String str;

    /* constructors */

    protected LightweightRule(AlgebraTerm left, AlgebraTerm right) {
    this.left = left;
    this.right = right;
    Vector<AlgebraVariable> vars = this.getVars();
    VarRenaming sigma = (VarRenaming)VarRenaming.create();
    int n = vars.size();
    for(int i=0; i<n; i++) {
        AlgebraVariable v = vars.elementAt(i);
        VariableSymbol vSymb = v.getVariableSymbol();
        Sort vSort = vSymb.getSort();
        sigma.putVar(vSymb, AlgebraVariable.create(VariableSymbol.create("x_"+i, vSort)));
    }
    this.transLeft = left.apply(sigma);
    this.transRight = right.apply(sigma);
    this.str = left.toString() + " -> " + right.toString();
    this.hashCode = (this.transLeft.toString() + " -> " + this.transRight.toString()).hashCode();
    }

    private LightweightRule(LightweightRule r) {
    this.left = r.left.deepcopy();
    this.right = r.right.deepcopy();
    this.transLeft = r.transLeft.deepcopy();
    this.transRight = r.transRight.deepcopy();
    this.hashCode = r.hashCode;
    this.str = r.str;
    }


    /** Constructor for a lightweight rule.
     */
    public static LightweightRule create(AlgebraTerm left, AlgebraTerm right) {
    return new LightweightRule(left.deepcopy(), right.deepcopy());
    }

    /** Constructor for a lightweight rule.
     */
    public static LightweightRule create(Rule r) {
    return new LightweightRule(r.getLeft().deepcopy(), r.getRight().deepcopy());
    }

    private static LightweightRule create(LightweightRule r) {
    return new LightweightRule(r);
    }

    /** Returns a rule which is constructed using this lightweight rule.
     */
    public Rule toRule() {
    return Rule.create(this.left, this.right);
    }

    /** Returns an equation which is constructed using this lightweight rule.
     */
    public LightweightEquation toLightweightEquation() {
    return LightweightEquation.create(this.left, this.right);
    }

    /** Returns the lenght of this rule, i.e. the sum on the lenghts of both
     * side.
     */
    public int length() {
    return this.left.length()+this.right.length();
    }

    @Override
    public boolean equals(Object o) {
    LightweightRule r;
    try {
        r = (LightweightRule)o;
    }
    catch(ClassCastException e) {
        return false;
    }
    return this.transLeft.equals(r.transLeft) &&
           this.transRight.equals(r.transRight);
    }

    /** Return the left hand side of this rule.
     */
    public AlgebraTerm getLeft() {
    return this.left;
    }

    /** Return the right hand side of this rule.
     */
    public AlgebraTerm getRight() {
    return this.right;
    }

    /** Return the normalized left hand side of this rule.
     */
    public AlgebraTerm getTransLeft() {
    return this.transLeft;
    }

    /** Return the normalized right hand side of this rule.
     */
    public AlgebraTerm getTransRight() {
    return this.transRight;
    }

    /** Returns a new rule where the right hand side is the normal form
     * w.r.t. <code>R</code> of this rules right hand side.
     */
    public LightweightRule normalizeRight(LightweightRules R) {
    return LightweightRule.create(this.left, this.right.normalize(R.toRules()));
    }

    /** Returns a new rule where the left hand side is the normal form
     * w.r.t. <code>R</code> of this rules left hand side.
     */
    public LightweightRule normalizeLeft(LightweightRules R) {
    return LightweightRule.create(this.left.normalize(R.toRules()), this.right);
    }

    /** Returns true if the left hand side of this rule is reducible by
     * <code>R</code>.
     */
    public boolean isLeftReducible(LightweightRule r) {
    Collection<Rule> dummy = new LinkedHashSet<Rule>();
    dummy.add(r.toRule());
    return !this.left.isNormal(dummy);
    }

    @Override
    public int hashCode() {
    return this.hashCode;
    }

    public LightweightRule deepcopy() {
    return LightweightRule.create(this);
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

    private Vector<AlgebraVariable> getVars() {
    Vector<AlgebraVariable> res = this.getVars(this.left);
    this.merge(res, this.getVars(this.right));
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
