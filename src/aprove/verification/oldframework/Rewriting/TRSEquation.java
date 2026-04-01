package aprove.verification.oldframework.Rewriting ;

import java.io.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/** Representation of an equation for equational rewriting.
 *  @author Stephan Falke
 *  @version $Id$
 */

public class TRSEquation implements Checkable, HTML_Able, LaTeX_Able, Serializable {

    protected AlgebraTerm oneSide, otherSide;
    private boolean sameHash;

    /* constructors */

    protected TRSEquation(AlgebraTerm oneSide, AlgebraTerm otherSide) {
    this.oneSide = oneSide;
    this.otherSide = otherSide;
        this.sameHash = (oneSide.hashCode() == otherSide.hashCode());
    }

    /** Constructor for an equations.
     */
    public static TRSEquation create(AlgebraTerm oneSide, AlgebraTerm otherSide) {
    return new TRSEquation(oneSide, otherSide);
    }

    public TRSEquation createWithFriendlyNames(FreshNameGenerator ngen, Program prog) {
    AlgebraTerm t1 = this.oneSide.createWithFriendlyNames(ngen, prog);
    AlgebraTerm t2 = this.otherSide.createWithFriendlyNames(ngen, prog);
    if (t1 == null || t2 == null) {
        return null;
    }
    return TRSEquation.create(t1, t2);
    }

    // acessor methods

    public AlgebraTerm getOneSide() {
    return this.oneSide;
    }

    public AlgebraTerm getOtherSide() {
    return this.otherSide;
    }

    /**
     * Compute the number of function symbols in this rule.
     */
    public int length() {
        return this.oneSide.length() + this.otherSide.length();
    }

    @Override
    public boolean equals(Object o) {
    TRSEquation e = (TRSEquation)o;
    return (this.oneSide.equals(e.oneSide) && this.otherSide.equals(e.otherSide))
        || (this.oneSide.equals(e.otherSide) && this.otherSide.equals(e.oneSide));
    }

    @Override
    public int hashCode() {
        if (!this.sameHash) {
            return this.toString().hashCode();
        }
        String s1 = this.oneSide.toString() + " == " + this.otherSide.toString();
        String s2 = this.otherSide.toString() + " == " + this.oneSide.toString();
        return Math.min(s1.hashCode(), s2.hashCode());
    }

    /** Returns a shallow copy of this object, i.e. an equation that uses the
     *  same terms.
     *  <p>
     *  Note: Changing the terms of the copied equation will result in
     *  changes to the original equation!
     */
    public TRSEquation shallowcopy() {
    return TRSEquation.create(this.oneSide, this.otherSide);
    }

    /** Returns a deep copy of this object, i.e. an equation that has the
     *  same structure and uses the same symbols.
     */
    public TRSEquation deepcopy() {
    return TRSEquation.create(this.oneSide.deepcopy(), this.otherSide.deepcopy());
    }

    // other accessors

    /** Return a string representation of this rule.
     */
    @Override
    public String toString() {
    StringBuffer temp = new StringBuffer();
    temp.append(this.oneSide.toString()+" == "+this.otherSide.toString());
    return temp.toString();
    }

    /** Return a HTML representation of this rule.
     */
    @Override
    public String toHTML() {
    StringBuffer temp = new StringBuffer();
    if(this.oneSide.hashCode() < this.otherSide.hashCode()) {
        temp.append(this.oneSide.toHTML()+" == "+this.otherSide.toHTML());
    }
    else {
        temp.append(this.otherSide.toHTML()+" == "+this.oneSide.toHTML());
    }
    return temp.toString();
    }

    @Override
    public String toLaTeX() {
        StringBuffer temp = new StringBuffer();
        temp.append("$"+this.oneSide.toLaTeX()+"$ & $\\approx$ & $"+this.otherSide.toLaTeX()+"$");
        return temp.toString();
    }

    public String toGrayLaTeX() {
        StringBuffer temp = new StringBuffer();
        temp.append("${\\lightgray "+this.oneSide.toLaTeX()+"}$ & ${\\lightgray \\approx}$ & ${\\lightgray "+this.otherSide.toLaTeX()+"}$");
        return temp.toString();
    }

    public String toSimpleLaTeX() {
        StringBuffer temp = new StringBuffer();
        temp.append("$"+this.oneSide.toSimpleLaTeX()+"$ &$\\approx$& $"+this.otherSide.toSimpleLaTeX()+"$");
        return temp.toString();
    }

    public String toGraySimpleLaTeX() {
        StringBuffer temp = new StringBuffer();
        temp.append("${\\lightgray "+this.oneSide.toSimpleLaTeX()+"}$ & ${\\lightgray\\approx}$ & ${\\lightgray "+this.otherSide.toSimpleLaTeX()+"}");
        return temp.toString()+"$";
    }

    @Override
    public void check() {
    this.check(new HashSet());
    }

    @Override
    public void check(Set checked) {
    if (!checked.contains(this)) {
        checked.add(this);
        if (this.oneSide ==  null) {
        throw new RuntimeException("oneSide must not be null");
        }
        if (this.otherSide == null) {
        throw new RuntimeException("otherSide must not be null");
        }
        this.oneSide.check(checked);
        this.otherSide.check(checked);
    }
    }

    /** Returns the set of variables used in this rule.
     */
    public Set<AlgebraVariable> getUsedVariables(){
    HashSet<AlgebraVariable> result = new HashSet<AlgebraVariable>();
    result.addAll(this.oneSide.getVars());
    result.addAll(this.otherSide.getVars());
    return result;
    }

    // cp

    /** Replace all variables by new variables, where variables from
     *  the given set are not allowed for use. Equal variables occuring
     *  more than once are replaced by the same variable.
     */
    public TRSEquation replaceVariables(Set<AlgebraVariable> usedVariables) {
    FreshVarGenerator generator = new FreshVarGenerator(usedVariables);
    AlgebraTerm leftTerm = this.oneSide.deepcopy();
    AlgebraTerm rightTerm = this.otherSide.deepcopy();
    HashSet<AlgebraVariable> variableSet = new HashSet<AlgebraVariable>(this.oneSide.getVars());
    variableSet.addAll(this.otherSide.getVars());
    AlgebraSubstitution sub = AlgebraSubstitution.create();
    Iterator i = variableSet.iterator();
    while (i.hasNext()) {
        AlgebraVariable oldVariable = (AlgebraVariable)i.next();
        AlgebraVariable newVariable = generator.getFreshVariable(oldVariable, true);
        sub.put(oldVariable.getVariableSymbol(), newVariable);
    }
    leftTerm = leftTerm.apply(sub);
    rightTerm = rightTerm.apply(sub);
        return TRSEquation.create(leftTerm, rightTerm);
    }


    /** Returns true if the given symbol occurs as the root symbol of
     * either side.
     */
    public boolean hasRootSymbol(Symbol symbol) {
    return this.oneSide.getSymbol().equals(symbol) || this.otherSide.getSymbol().equals(symbol);
    }

    /** Returns the set of all function symbols in this equation.
     */
    public Set<SyntacticFunctionSymbol> getFunctionSymbols() {
        Set<SyntacticFunctionSymbol> funcs = new LinkedHashSet<SyntacticFunctionSymbol>();
        funcs.addAll(this.oneSide.getFunctionSymbols());
        funcs.addAll(this.otherSide.getFunctionSymbols());
        return funcs;
    }

    /** Returns the set of all constructor symbols in this equation.
     */
    public Set<SyntacticFunctionSymbol> getConstructorSymbols() {
        Set<SyntacticFunctionSymbol> funcs = new LinkedHashSet<SyntacticFunctionSymbol>();
        funcs.addAll(this.oneSide.getConstructorSymbols());
        funcs.addAll(this.otherSide.getConstructorSymbols());
        return funcs;
    }

    /** Determines whether this equation is permutative, i.e. do all symbols occur the same time on both sides?
     */
    public boolean isPermutative() {
    Map counterss = new HashMap();
    Map counterst = new HashMap();
    TRSEquation.fill(this.oneSide, counterss);
    TRSEquation.fill(this.otherSide, counterst);
    return counterss.equals(counterst);
    }

    private static void fill(AlgebraTerm t, Map map) {
    Symbol symb = t.getSymbol();
    TRSEquation.incByOne(symb, map);
    if(symb instanceof SyntacticFunctionSymbol) {
        Iterator i = t.getArguments().iterator();
        while(i.hasNext()) {
        TRSEquation.fill((AlgebraTerm)i.next(), map);
        }
    }
    }

    private static void incByOne(Symbol symb, Map map) {
    Object o = map.get(symb);
    int oldc = 0;
    if(o!=null) {
        oldc = ((Integer)o).intValue();
    }
    map.put(symb, Integer.valueOf(oldc+1));
    }

    /** Determines whether this equation involes only constructors and variables.
     */
    public boolean isConstructorEquation() {
    Set<SyntacticFunctionSymbol> symbs = this.oneSide.getFunctionSymbols();
    symbs.addAll(this.otherSide.getFunctionSymbols());
    Iterator i = symbs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
        if(fun instanceof DefFunctionSymbol) {
        return false;
        }
    }
    return true;
    }

    /** Returns the root symbols of both sides of this equation.
     */
    public Set<SyntacticFunctionSymbol> getRootSymbols() {
    Set<SyntacticFunctionSymbol> res = new LinkedHashSet<SyntacticFunctionSymbol>();
    Symbol symb = this.oneSide.getSymbol();
    if(!(symb instanceof VariableSymbol)) {
        res.add((SyntacticFunctionSymbol) symb);
    }
    symb = this.otherSide.getSymbol();
    if(!(symb instanceof VariableSymbol)) {
        res.add((SyntacticFunctionSymbol) symb);
    }
    return res;
    }

    /** Determines whether this equation is collapsing.
     */
    public boolean isCollapsing() {
    return (this.oneSide.isVariable() || this.otherSide.isVariable());
    }

    /** Determines whether this equation is linear.
     */
    public boolean isLinear() {
    return (this.oneSide.isLinear() || this.otherSide.isLinear());
    }

    /** Determines whether both sides have the same variables.
     */
    public boolean hasIdenticalVars() {
    return this.oneSide.getVars().equals(this.otherSide.getVars());
    }

    /** Determines whether this equation has identical unique variables.
     */
    public boolean hasIdenticalUniqueVars() {
    return (this.isLinear() && this.hasIdenticalVars());
    }

    public static Set<SyntacticFunctionSymbol> getFunctionSymbols(Collection<TRSEquation> eqs) {
        return EquationalTheory.create(eqs).getFunctionSymbols();
    }

}
