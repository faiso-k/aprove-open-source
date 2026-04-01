package aprove.verification.oldframework.Rewriting ;

/** This representation of term rewriting rules is used for the
 *  internal representation of all input languages.
 *  @author Peter Schneider-Kamp
 *  @version $Id$
 *  @bug Conditional rules are not handled in many cases (e.g. replaceVariables)
 */

import java.io.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

public class Rule implements Checkable, PairOfTerms, HTML_Able, LaTeX_Able, PLAIN_Able, Serializable {

    protected List<Rule> conds;
    protected AlgebraTerm left, right;

    /* constructors */

    protected Rule(List<Rule> conds, AlgebraTerm left, AlgebraTerm right) {
    this.conds = conds;
    this.left = left;
    this.right = right;
    }

    /** Constructor for a conditional rule, i.e. a rule that gets
     *  a list of non-conditional rules as preconditions.
     */
    public static Rule create(List<Rule> conds, AlgebraTerm left, AlgebraTerm right) {
    // check if all rules in conds are non-conditional
    Iterator i = conds.iterator();
    while (i.hasNext()) {
        Rule r = (Rule)i.next();
        if (r.conds.size() != 0) {
        throw new RuntimeException("Internal Error: Cannot initialize conditions with conditional rules.");
        }
    }
    return new Rule(conds, left, right);
    }

    /** Constructor for a non-conditional rule.
     */
    public static Rule create(AlgebraTerm left, AlgebraTerm right) {
    return new Rule(new Vector<Rule>(), left, right);
    }

    public Rule createWithFriendlyNames(FreshNameGenerator ngen, Program prog) {
    List<Rule> newconds = new Vector<Rule>();
    if (!(this.conds == null || this.conds.isEmpty())) {
        Iterator it = this.conds.iterator();
        while (it.hasNext()) {
        newconds.add(((Rule)it.next()).createWithFriendlyNames(ngen, prog));
        }
    }
    return Rule.create(newconds, this.left.createWithFriendlyNames(ngen, prog), this.right.createWithFriendlyNames(ngen, prog));
    }

    // methods for the PairOfTerms interface

    @Override
    public AlgebraTerm getLeft() {
    return this.left;
    }

    @Override
    public AlgebraTerm getRight() {
    return this.right;
    }

    /**
     * Compute the number of function symbols in this rule.
     */
    public int length() {
        return this.left.length() + this.right.length();
    }

    @Override
    public boolean equals(Object o) {
    Rule r = (Rule)o;
    return this.conds.equals(r.conds) &&
        this.left.equals(r.left) &&
           this.right.equals(r.right);
    }

    @Override
    public int hashCode() {
    return this.toString().hashCode();
    }

    /* Forbidden for security's and sanity's sake */
    @Override
    protected Object clone() {
    throw new RuntimeException("clone deprecated -- use deepcopy / shallowcopy instead");
    }

    /** Returns a shallow copy of this object, i.e. a rule that uses the
     *  same conditions and terms.
     *  <p>
     *  Note: Changing the conditons or terms of the copied rule will result in
     *  changes to the original rule!
     */
    public Rule shallowcopy() {
    return Rule.create(new Vector<Rule>(this.conds), this.left, this.right);
    }

    /** Returns a deep copy of this object, i.e. a rule that has the
     *  same structure and uses the same symbols.
     *  <p>
     *  Note: Changing the symbols will result in changes to the
     *  original term.
     */
    public Rule deepcopy() {
    Vector<Rule> newConds = new Vector<Rule>();
    Iterator i = this.conds.iterator();
    while (i.hasNext()) {
        Rule r = (Rule)i.next();
        newConds.add(r.deepcopy());
    }
    return Rule.create(newConds, this.left.deepcopy(), this.right.deepcopy());
    }

    // other accessors

    public List<Rule> getConds() {
    return this.conds;
    }

    public Rule getCond(int index) {
    return this.conds.get(index);
    }

    /** Return a string representation of this rule.
     */
    @Override
    public String toString() {
    StringBuffer temp = new StringBuffer();
    if (this.conds != null && this.conds.size() != 0) {
        for (Iterator i = this.conds.iterator(); i.hasNext();) {
        temp.append(((Rule)i.next()).toString());
        if (i.hasNext()) {
            temp.append(", ");
        }
        }
        temp.append(" | ");
    }
    temp.append(this.left.toString()+" -> "+this.right.toString());
    return temp.toString();
    }

    /** Return a HTML representation of this rule.
     */
    @Override
    public String toHTML() {
        StringBuffer temp = new StringBuffer();
        if (this.conds != null && this.conds.size() != 0) {
            for (Iterator i = this.conds.iterator(); i.hasNext();) {
            temp.append(((Rule)i.next()).toHTML());
            if (i.hasNext()) {
                temp.append(", ");
            }
            }
            temp.append(" | ");
        }
        temp.append(this.left.toHTML()+" -&gt; "+this.right.toHTML());
        return temp.toString();
    }

    @Override
    public String toLaTeX() {
        StringBuffer temp = new StringBuffer();
        if (this.conds != null && this.conds.size() != 0) {
        temp.append("$");
            for (Iterator i = this.conds.iterator(); i.hasNext();) {
            Rule tmprule = (Rule) i.next();
            temp.append(tmprule.left.toLaTeX()+"\\to "+tmprule.right.toLaTeX());
            if (i.hasNext()) {
                temp.append(", ");
            }
            }
            temp.append("$ & $|$ & $");
            temp.append(this.left.toLaTeX()+" \\to "+this.right.toLaTeX()+"$");
        //} else if (this.conds != null && this.conds.size() == 0) {
            //temp.append(" & & ");
            //temp.append(this.left.toLaTeX()+" \\to "+this.right.toLaTeX());
        } else {
          temp.append("$"+this.left.toLaTeX()+"$ &$\\to$& $"+this.right.toLaTeX()+"$");
        }
        return temp.toString();
    }

    public String toSimpleLaTeX() {
        StringBuffer temp = new StringBuffer();
        if (this.conds != null && this.conds.size() != 0) {
        temp.append("$");
            for (Iterator i = this.conds.iterator(); i.hasNext();) {
            Rule tmprule = (Rule) i.next();
            temp.append(tmprule.left.toSimpleLaTeX()+"\\to "+tmprule.right.toSimpleLaTeX());
            if (i.hasNext()) {
                temp.append(", ");
            }
            }
            temp.append("$ & $|$ & $");
            temp.append(this.left.toSimpleLaTeX()+" \\to "+this.right.toSimpleLaTeX());
        //} else if (this.conds != null && this.conds.size() == 0) {
            //temp.append(" & & ");
            //temp.append(this.left.toLaTeX()+" \\to "+this.right.toLaTeX());
        } else {
          temp.append("$"+this.left.toSimpleLaTeX()+"$ &$\\to$& $"+this.right.toSimpleLaTeX()+"$");
        }
        return temp.toString();
    }

    public String toGrayLaTeX() {
        StringBuffer temp = new StringBuffer();
        if (this.conds != null && this.conds.size() != 0) {
        temp.append("$");
            for (Iterator i = this.conds.iterator(); i.hasNext();) {
            Rule tmprule = (Rule) i.next();
            temp.append("{\\lightgray "+tmprule.left.toLaTeX()+"} &{\\lightgray\\to}& {\\lightgray "+tmprule.right.toLaTeX());
            if (i.hasNext()) {
                temp.append(",} ");
            } else {
                temp.append("}");
            }
            }
            temp.append("$ & ${\\lightgray|}$ & $");
            temp.append(this.left.toLaTeX()+"{\\lightgray \\to}"+this.right.toLaTeX()+"$");
        //} else if (this.conds != null && this.conds.size() == 0) {
            //temp.append(" & & ");
            //temp.append(this.left.toLaTeX()+" \\to "+this.right.toLaTeX());
        } else {
          temp.append("${\\lightgray "+this.left.toLaTeX()+"}$ & ${\\lightgray\\to}$ & ${\\lightgray "+this.right.toLaTeX()+"}$");
        }
        return temp.toString();
    }

    public String toGraySimpleLaTeX() {
        StringBuffer temp = new StringBuffer();
        if (this.conds != null && this.conds.size() != 0) {
        temp.append("$");
            for (Iterator i = this.conds.iterator(); i.hasNext();) {
            Rule tmprule = (Rule) i.next();
            temp.append("{\\lightgray "+tmprule.left.toSimpleLaTeX()+"}$ & ${\\lightgray\\to}$ & ${\\lightgray "+tmprule.right.toSimpleLaTeX());
            if (i.hasNext()) {
                temp.append(",} ");
            } else {
                temp.append("}");
            }
            }
            temp.append("$ & ${\\lightgray|}$ & $");
            temp.append(this.left.toSimpleLaTeX()+"{\\lightgray \\to}"+this.right.toSimpleLaTeX());
        //} else if (this.conds != null && this.conds.size() == 0) {
            //temp.append(" & & ");
            //temp.append(this.left.toLaTeX()+" \\to "+this.right.toLaTeX());
        } else {
          temp.append("${\\lightgray "+this.left.toSimpleLaTeX()+"}$ & ${\\lightgray\\to}$ & ${\\lightgray "+this.right.toSimpleLaTeX()+"}");
        }
        return temp.toString()+"$";
    }

    public String toCondLaTeX() {
        StringBuffer temp = new StringBuffer();
        if (this.conds != null && this.conds.size() != 0) {
            temp.append("$");
            for (Iterator i = this.conds.iterator(); i.hasNext();) {
            Rule tmprule = (Rule) i.next();
            temp.append(tmprule.left.toLaTeX()+"\\to "+tmprule.right.toLaTeX());
            if (i.hasNext()) {
                temp.append(", $ & & \\\\\n $");
            }
            }
            temp.append("$ & $|$ & $");
            temp.append(this.left.toLaTeX()+" \\to "+this.right.toLaTeX());
        } else {
            temp.append("& & $");
            temp.append(this.left.toLaTeX()+" \\to "+this.right.toLaTeX());
        }
        return temp.toString()+"$";
    }

    public String toCondSimpleLaTeX() {
        StringBuffer temp = new StringBuffer();
        if (this.conds != null && this.conds.size() != 0) {
            temp.append("$");
            for (Iterator i = this.conds.iterator(); i.hasNext();) {
            Rule tmprule = (Rule) i.next();
            temp.append(tmprule.left.toSimpleLaTeX()+"\\to "+tmprule.right.toSimpleLaTeX());
            if (i.hasNext()) {
                temp.append(", ");
            }
            }
            temp.append("$ & $|$ & $");
            temp.append(this.left.toSimpleLaTeX()+" \\to "+this.right.toSimpleLaTeX());
        } else {
            temp.append("$ & & $");
            temp.append(this.left.toSimpleLaTeX()+" \\to "+this.right.toSimpleLaTeX());
        }
        return temp.toString()+"$";
    }

    public String toTTT() {
        StringBuffer temp = new StringBuffer();
        temp.append(this.left.toTTT()+" -> "+this.right.toTTT());
        return temp.toString();
    }

    @Override
    public String toPLAIN() {
        return this.toString();
    }

    public String toTERMPTATION(FreshNameGenerator vars, FreshNameGenerator funcs) {
        StringBuffer temp = new StringBuffer();
        temp.append(this.left.toTERMPTATION(vars, funcs)+" -> "+this.right.toTERMPTATION(vars, funcs));
        return temp.toString();
    }

    public String toHASKELL() {
        StringBuffer temp = new StringBuffer();
        String left = this.left.toHASKELL();
        if (left.charAt(0) == '(') {
            left = left.substring(1, left.length()-1);
        }
        String right = this.right.toHASKELL();
        if (right.charAt(0) == '(') {
            right = right.substring(1, right.length()-1);
        }
        temp.append(left+" = "+right);
        return temp.toString();
    }

    /* extremely verbose string serialization - DEBUG */
    public String verboseToString() {
    StringBuffer temp = new StringBuffer();
    if (this.conds != null && this.conds.size() != 0) {
        for (Iterator i = this.conds.iterator(); i.hasNext();) {
        temp.append(((Rule)i.next()).verboseToString());
        if (i.hasNext()) {
            temp.append(", ");
        }
        }
        temp.append(" | ");
    }
    temp.append(this.left.verboseToString()+" -> "+this.right.verboseToString());
    return temp.toString();
    }

    @Override
    public void check() {
    this.check(new HashSet());
    }
    @Override
    public void check(Set checked) {
    if (!checked.contains(this)) {
        checked.add(this);
        if (this.left ==  null) {
        throw new RuntimeException("left must not be null");
        }
        if (this.right == null) {
        throw new RuntimeException("right must not be null");
        }
        if (this.conds == null) {
        throw new RuntimeException("conds must not be null");
        }
        for (Iterator i=this.conds.iterator(); i.hasNext();) {
        ((Rule)i.next()).check(checked);
        }
        this.left.check(checked);
        this.right.check(checked);
    }
    }

    /** Rreturns the set of variables used in this rule.
     */
    public Set<AlgebraVariable> getUsedVariables(){
    Set<AlgebraVariable> result = new LinkedHashSet<AlgebraVariable>();
    result.addAll(this.left.getVars());
    result.addAll(this.right.getVars());
    Iterator it = this.getConds().iterator();
    while (it.hasNext()) {
        result.addAll(((Rule)it.next()).getUsedVariables());
    }
    return result;
    }

    /** Replace all variables by new variables, where variables from
     *  the given set are not allowed for use. Equal variables occuring
     *  more than once are replaced by the same variable.
     */
    public Rule replaceVariables(Set<AlgebraVariable> usedVariables) {
        FreshVarGenerator generator = new FreshVarGenerator(usedVariables);
        return this.replaceVariables(generator);
    }

    public Rule replaceVariables(FreshVarGenerator generator) {
        AlgebraTerm leftTerm = this.left;
        AlgebraTerm rightTerm = this.right;
        HashSet<AlgebraVariable> variableSet = new HashSet<AlgebraVariable>(this.left.getVars());
        // According to the Definition, this should not be neccessary.
        variableSet.addAll(this.right.getVars());
        AlgebraSubstitution sub = AlgebraSubstitution.create();
        Iterator i = variableSet.iterator();
        while (i.hasNext()) {
            AlgebraVariable oldVariable = (AlgebraVariable)i.next();
            AlgebraVariable newVariable = generator.getFreshVariable(oldVariable, true);
            sub.put(oldVariable.getVariableSymbol(), newVariable);
        }

        leftTerm = leftTerm.apply(sub);
        rightTerm = rightTerm.apply(sub);

        List<Rule> renamedConditions = new Vector<Rule>();
        for(Rule condition : this.conds) {
            renamedConditions.add(Rule.create(condition.getLeft().apply(sub), condition.getRight().apply(sub)));
        }
        return Rule.create(renamedConditions, leftTerm, rightTerm);
    }

    /** Returns true if the given symbol concurs with the root symbol of
     *  the left term.
     */
    public boolean hasRootSymbol(Symbol symbol) {
    return this.getRootSymbol().equals(symbol);
    }

    /** Returns the root symbol of this rule.
     */
    public SyntacticFunctionSymbol getRootSymbol() {
        return (SyntacticFunctionSymbol)this.left.getSymbol();
    }

    /** Returns the set of all function symbols in this rule.
     */
    public Set<SyntacticFunctionSymbol> getFunctionSymbols() {
        Set<SyntacticFunctionSymbol> funcs = new LinkedHashSet<SyntacticFunctionSymbol>();
        funcs.addAll(this.left.getFunctionSymbols());
        funcs.addAll(this.right.getFunctionSymbols());
        return funcs;
    }

    /**
     * Check if this rule is deterministic.
     * @return True, iff the variable conditions for rules in CTRS hold.
     */
    public boolean isDeterministic() {
        Set<AlgebraVariable> valid = new LinkedHashSet<AlgebraVariable>(this.left.getVars());
    Iterator i = this.getConds().iterator();
        while (i.hasNext()) {
            Rule cond = (Rule)i.next();
            if (!valid.containsAll(cond.getLeft().getVars())) {
                return false;
            }
            valid.addAll(cond.getRight().getVars());
        }
    return valid.containsAll(this.getRight().getVars());
    }

    /**
     * Berechnet alle definierten Funktionssymbole, die in
     * den rules vorkommen
     */
    public static Set<DefFunctionSymbol> getDefFunctionSymbols(Collection<Rule> rules) {
        HashSet<DefFunctionSymbol> fs = new HashSet<DefFunctionSymbol>();
        Iterator i = rules.iterator();
        Rule r;
        while (i.hasNext()) {
            r = (Rule)i.next();
            // es reicht aus, links zu schauen, da Symbole rechts eh aufgrund
            // der usable-rules Bedingung auch links auftauchen!
            // RT:
            // this not true for active any more: changed to both sides
            fs.addAll(r.getLeft().getDefFunctionSymbols());
            fs.addAll(r.getRight().getDefFunctionSymbols());
        }
        return fs;
    }

    /* Computes the symbols that are used as tuple symbols in the dps.
     */
    public static Set<SyntacticFunctionSymbol> getTupleSymbols(Collection<Rule> dps) {
        Set<SyntacticFunctionSymbol> tupleSymbols = new LinkedHashSet<SyntacticFunctionSymbol>();
        Iterator i = dps.iterator();
        while(i.hasNext()) {
        Rule dp = (Rule)i.next();
        tupleSymbols.add((SyntacticFunctionSymbol) dp.getLeft().getSymbol());
        tupleSymbols.add((SyntacticFunctionSymbol) dp.getRight().getSymbol());
    }
    return tupleSymbols;
    }

    /* Computes the inner function symbols that occur in the dps.
     */
    public static Set<SyntacticFunctionSymbol> getInnerFunctionSymbols(Collection<Rule> dps) {
        Set<SyntacticFunctionSymbol> innerSymbols = new LinkedHashSet<SyntacticFunctionSymbol>();
        Iterator i = dps.iterator();
        while(i.hasNext()) {
        Rule dp = (Rule)i.next();
        innerSymbols.addAll(dp.getLeft().getInnerFunctionSymbols());
        innerSymbols.addAll(dp.getRight().getInnerFunctionSymbols());
    }
    return innerSymbols;
    }

    /**
     * Berechnet alle Konstruktoren, die in
     * den rules vorkommen
     */
    public static Set<SyntacticFunctionSymbol> getConstructorSymbols(Collection<Rule> rules) {
        HashSet<SyntacticFunctionSymbol> fs = new HashSet<SyntacticFunctionSymbol>();
        Iterator i = rules.iterator();
        Rule r;
        while (i.hasNext()) {
            r = (Rule)i.next();
            fs.addAll(r.getLeft().getConstructorSymbols());
            fs.addAll(r.getRight().getConstructorSymbols());
        }
        return fs;
    }

    /**
     * Computes all function symbols that occur in the rules.
     */
    public static Set<SyntacticFunctionSymbol> getFunctionSymbols(Collection<Rule> rules) {
        Set<SyntacticFunctionSymbol> fs = new LinkedHashSet<SyntacticFunctionSymbol>();
        Iterator i = rules.iterator();
        while (i.hasNext()) {
            Rule r = (Rule)i.next();
            fs.addAll(r.getLeft().getFunctionSymbols());
            fs.addAll(r.getRight().getFunctionSymbols());
        }
        return fs;
    }

    /**
     * Computes all function symbols that occur in rhs of the rules.
     */
    public static Set<SyntacticFunctionSymbol> getRightFunctionSymbols(Collection<Rule> rules) {
        HashSet<SyntacticFunctionSymbol> fs = new HashSet<SyntacticFunctionSymbol>();
        Iterator i = rules.iterator();
        Rule r;
        while (i.hasNext()) {
            r = (Rule)i.next();
            fs.addAll(r.getRight().getFunctionSymbols());
        }
        return fs;
    }

    /**
     * calculates root-symbols of given rules for the left sides
     */
    public static Set<SyntacticFunctionSymbol> getLeftRootSymbols(Collection<Rule> rules) {
        Iterator i = rules.iterator();
        Set<SyntacticFunctionSymbol> syms = new LinkedHashSet<SyntacticFunctionSymbol>();
        while (i.hasNext()) {
            Rule r = (Rule) i.next();
            syms.add(r.getRootSymbol());
        }
        return syms;
    }

    /** Splits rules according to condition.
     *  This function is destructive.
     *  FIXME: Variablerenaming might yield problems when different rules
     *  introduce different new variables in conditions or the lhs with
     *  the same name.
     */
    public static Vector splitAtCondition(Vector<Rule> rules, int n) {
    Vector split = new Vector();
    while (!rules.isEmpty()) {
        Rule r = rules.remove(0);
        AlgebraTerm gen_term = n == -1 ? r.getLeft() : r.getConds().get(n).getRight();
        Vector<Rule> subset = new Vector<Rule>();
        subset.add(r);
        Iterator r_it = rules.iterator();
        while (r_it.hasNext()) {
        r = (Rule)r_it.next();
        AlgebraTerm t = n == -1 ? r.getLeft() : r.getConds().get(n).getRight();
        try {
            AlgebraSubstitution varren = gen_term.matches(t);
            // Same rhs of condition (same lhs is assumed),
            // thus this rule has to be added.
            Vector<Rule> newconds = new Vector<Rule>();
            Iterator c_it = r.getConds().iterator();
            for (int i=0; c_it.hasNext(); i++) {
            Rule cond = (Rule)c_it.next();
            if (i < n) {
                newconds.add(cond);
            }
            else {
                AlgebraTerm ncleft = cond.getLeft().apply(varren);
                AlgebraTerm ncright = cond.getRight().apply(varren);
                newconds.add(Rule.create(ncleft, ncright));
            }
            }
            subset.add(Rule.create(newconds, r.getLeft(), r.getRight().apply(varren)));
            r_it.remove();
        }
        catch (UnificationException e) { }
        }
        split.add(subset);
    }
    return split;
    }

    /**
     * Checks if this rule only contains unary function symbols
     */
    public boolean isUnary() {
        return this.left.isUnary() && this.right.isUnary();
    }

    /**
     * Checks if this rule only contains unary function symbols
     * or constants
     */
    public boolean isMaxUnary() {
        return this.left.isMaxUnary() && this.right.isMaxUnary();
    }

    /**
     * Checks if this rule only contains unary function symbols
     * or constants
     */
    public boolean isStringRewriting() {
        return this.isMaxUnary();
    }

    /**
     * Checks whether this rule is collapsing, i.e. the rhs
     * is a variable.
     */
    public boolean isCollapsing() {
        return this.getRight().isVariable();
    }

    /**
     * Reverses lhs and rhs of this rule.
     * @return A new rule with lhs and rhs reversed.
     */
    public Rule reverse(FreshNameGenerator fg) {
        return Rule.create(this.left.reverse(fg), this.right.reverse(fg));
    }

    /**
     * Updates which symbols are constructors and which are defined function symbols.
     */
    public Rule updateConsDef(Set<SyntacticFunctionSymbol> toCons, Set<SyntacticFunctionSymbol> toDef) {
        return Rule.create(Rule.updateConsDef(this.conds,toCons,toDef),this.left.updateConsDef(toCons, toDef), this.right.updateConsDef(toCons, toDef));
    }

    /**
     * Updates which symbols are constructors and which are defined function symbols.
     */
    private static List<Rule> updateConsDef(List<Rule> rules, Set<SyntacticFunctionSymbol> toCons, Set<SyntacticFunctionSymbol> toDef) {
        List<Rule> res = new Vector<Rule>();
        for (Rule r : rules) {
           res.add(r.updateConsDef(toCons,toDef));
        }
        return res;
    }

    public boolean isRightLinear() {
        return this.right.isLinear();
    }

    public Rule apply(AlgebraSubstitution sub) {
        List<Rule> res = new Vector<Rule>();
        for (Rule cond : this.getConds()) {
            res.add(cond.apply(sub));
        }
        return Rule.create(res,this.getLeft().apply(sub),this.getRight().apply(sub));
    }

    public aprove.verification.dpframework.BasicStructures.Rule toNewRule() {
        return aprove.verification.dpframework.BasicStructures.Rule.create((aprove.verification.dpframework.BasicStructures.TRSFunctionApplication)this.getLeft().toNewTerm(), this.getRight().toNewTerm());
    }

    public aprove.verification.dpframework.BasicStructures.GeneralizedRule toNewGeneralizedRule() {
        return aprove.verification.dpframework.BasicStructures.GeneralizedRule.create((aprove.verification.dpframework.BasicStructures.TRSFunctionApplication)this.getLeft().toNewTerm(), this.getRight().toNewTerm());
    }

}
