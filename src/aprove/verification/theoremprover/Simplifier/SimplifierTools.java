package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class SimplifierTools {
    /** Returns the rule of the defining rules of f that has a
     *  corresponding lhs.
     */
    public static AlgebraTerm getCorrespondentRuleRight(Set<Rule> rules, List<AlgebraTerm> ts, List<Rule> fconds) {
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule gr = (Rule)it.next();
        List<Rule> gconds = gr.getConds();
        try {
        boolean allrenaming = true;
        Iterator ga_it = gr.getLeft().getArguments().iterator();
        Iterator fa_it = ts.iterator();
        AlgebraSubstitution sigma = AlgebraSubstitution.create();
        while (ga_it.hasNext()) {
            AlgebraTerm ga = (AlgebraTerm)ga_it.next();
            AlgebraTerm fa = (AlgebraTerm)fa_it.next();
            sigma = ga.matches(fa, sigma);
        }
        if (sigma.isVariableRenaming() && fconds.size()==gconds.size()) {
            Iterator gc_it = gconds.iterator();
            Iterator fc_it = fconds.iterator();
            boolean allCondsAreEqual = true;
            while (allCondsAreEqual && gc_it.hasNext()) {
            Rule gc = (Rule)gc_it.next();
            Rule fc = (Rule)fc_it.next();
            allCondsAreEqual = fc.getLeft().equals(gc.getLeft().apply(sigma)) && fc.getRight().equals(gc.getRight().apply(sigma));
            }
            if (allCondsAreEqual) {
            return gr.getRight().apply(sigma);
            }
        }
        }
        catch (Exception e) { }
    }
    return null;
    }

    public static Rule getCorrespondentRule(Set<Rule> rules, List<AlgebraTerm> ts, List<Rule> fconds) {
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule gr = (Rule)it.next();
        List<Rule> gconds = gr.getConds();
        try {
        boolean allrenaming = true;
        Iterator ga_it = gr.getLeft().getArguments().iterator();
        Iterator fa_it = ts.iterator();
        AlgebraSubstitution sigma = AlgebraSubstitution.create();
        while (ga_it.hasNext()) {
            AlgebraTerm ga = (AlgebraTerm)ga_it.next();
            AlgebraTerm fa = (AlgebraTerm)fa_it.next();
            sigma = ga.matches(fa, sigma);
        }
        if (sigma.isVariableRenaming() && fconds.size()==gconds.size()) {
            Iterator gc_it = gconds.iterator();
            Iterator fc_it = fconds.iterator();
            boolean allCondsAreEqual = true;
            while (allCondsAreEqual && gc_it.hasNext()) {
            Rule gc = (Rule)gc_it.next();
            Rule fc = (Rule)fc_it.next();
            allCondsAreEqual = fc.getLeft().equals(gc.getLeft().apply(sigma)) && fc.getRight().equals(gc.getRight().apply(sigma));
            }
            if (allCondsAreEqual) {
            return gr;
            }
        }
        }
        catch (Exception e) { }
    }
    return null;
    }


    /** lifts the matching into a previous condtion or into the lhs of the rule.
     *  @return A transformed rule if transformation was possible, null
     *  otherwise.
     */
    public static Rule liftMatching(Rule rule) {
    List<Rule> conds = rule.getConds();
    if (conds.isEmpty()) {
        return null;
    }
    Iterator it = conds.iterator();
    Rule cond = (Rule)it.next();
    if (!cond.getLeft().isVariable()) {
        return null;
    }
    AlgebraSubstitution sigma = AlgebraSubstitution.create();
    // Tells whether we have only seen variables on the lhs.
    boolean allvars = true;
    List<Rule> newconds = new Vector<Rule>();
    it = conds.iterator();
    while (allvars && it.hasNext() ) {
        cond = (Rule)it.next();
        AlgebraTerm left = cond.getLeft().apply(sigma);
        if (left.isVariable()) {

//        sigma.put((VariableSymbol)left.getSymbol(), cond.getRight());
        VariableSymbol lVarSym = (VariableSymbol)left.getSymbol();
        AlgebraSubstitution tau = AlgebraSubstitution.create();
        tau.put(lVarSym, cond.getRight().apply(sigma));
        sigma = sigma.compose(tau);

        }
        else {
        allvars = false;
        newconds.add(Rule.create(cond.getLeft().apply(sigma),cond.getRight().apply(sigma)));
        }
    }
    while (it.hasNext()) {
        cond = (Rule)it.next();
        AlgebraTerm s = cond.getRight().apply(sigma);
        AlgebraTerm t = cond.getLeft().apply(sigma);
        newconds.add(Rule.create(t, s));
    }
    AlgebraTerm left = rule.getLeft().apply(sigma);
    AlgebraTerm right = rule.getRight().apply(sigma);
    return Rule.create(newconds, left, right);
    }

    /** Returns a vector of positions p in t1 where t2 matches t1|p and
     *  there is no position p' with p' &lt; p and t2 matches t1|p.
     */
    protected static Vector<Position> getOutermostMatchingPositions(AlgebraTerm t1, AlgebraTerm t2) {
    Vector<Position> result = new Vector<Position>();
    Vector<AlgebraTerm> terms = new Vector<AlgebraTerm>();
    Vector<Position> positions = new Vector<Position>();
    terms.add(t1);
    positions.add(Position.create());
    while (!terms.isEmpty()) {
        Position p = (Position)positions.remove(0);
        AlgebraTerm t = (AlgebraTerm)terms.remove(0);
        Symbol sym = t.getSymbol();
        if (t2.isMatchable(t)) {
        result.add(p);
        }
        else if (sym instanceof SyntacticFunctionSymbol) {
        int i = 0;
        Iterator it = t.getArguments().iterator();
        while (it.hasNext()) {
            AlgebraTerm nt = (AlgebraTerm)it.next();
            terms.add(nt);
            Position np = p.shallowcopy();
            np.add(i);
            positions.add(np);
            i++;
        }
        }
    }
    return result;
    }

    /** Returns true iff the given set of rules are valid.
     */
    protected static boolean isValidSetOfRules(Set<Rule> rules) {
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        if (!((Rule)it.next()).isDeterministic()) {
        return false;
        }
    }
    return true;
    }


    /** Gets the type of a term from information in the rule
     */
    public static AlgebraTerm getTypeOfTerm(AlgebraTerm term, Rule r, TypeContext typeContext) {
        AlgebraTerm res = null;

        if (!term.isVariable()) {
            res = TypeTools.getResultTerm(typeContext.getSingleTypeOf(term.getSymbol()).getTypeMatrix());
        }
        else {
            Set<VariableSymbol> vars = new HashSet<VariableSymbol>();
            vars.add((VariableSymbol)term.getSymbol());
            res = SimplifierTools.getTypeOfVariables(vars, r, typeContext);
        }

        return res;
    }


    /** returns positions within a term
     *  where the variable symbol vsym is found
     */
    private static Set<Position> getVariablePositionsInTerm(VariableSymbol vsym, AlgebraTerm term) {
        Set<Position> res = new LinkedHashSet<Position>();
        Set<Position> positions = term.getPositions();
        for (Position pi : positions) {
            if(term.getSubterm(pi).getSymbol().equals(vsym)) {
                res.add(pi);
            }
        }
        return res;
    }


    /** Looks in the rule for an occurence of these variables, such that the
      * type of the variables can be determined from there
     */
    public static AlgebraTerm getTypeOfVariables(Set<VariableSymbol> vars, Rule r, TypeContext typeContext) {
        AlgebraTerm res = null;

        // check the lhs of the rule
        res = SimplifierTools.getTypeOfVariablesInTerm(vars, r.getLeft(), typeContext);

        if (res != null) {
            return res;
        }

        // there were no occurences in the lhs. Now check the conditions
        Iterator<Rule> c_it = r.getConds().iterator();
        while (c_it.hasNext() && (res == null)) {
            Rule cond = c_it.next();
            if (!cond.getRight().isVariable()) {
                res = SimplifierTools.getTypeOfVariablesInTerm(vars, cond.getRight(), typeContext);
            }
            else {
                if (vars.contains((VariableSymbol)cond.getRight().getSymbol())) {
                    if (!cond.getLeft().isVariable()) {
                        res = TypeTools.getResultTerm(typeContext.getSingleTypeOf(cond.getLeft().getSymbol()).getTypeMatrix());
                    }
                    else {
                        if (vars.add((VariableSymbol)cond.getLeft().getSymbol())) {
                            res = SimplifierTools.getTypeOfVariables(vars, r, typeContext);
                        }
                    }
                }
            }
        }

        return res;
    }


    /** Tries to get the type of the variables var from the term t
     */
    public static AlgebraTerm getTypeOfVariablesInTerm(Set<VariableSymbol> vars, AlgebraTerm t, TypeContext typeContext) {
        if (t.isVariable()) {
            return null;
        }

        AlgebraTerm res = null;
        Set<Position> positions = new LinkedHashSet<Position>();
        for(VariableSymbol var : vars) {
            positions.addAll(SimplifierTools.getVariablePositionsInTerm(var,t));
        }

        if (positions.iterator().hasNext()) {
            Position pi = positions.iterator().next();
            int j = pi.getLast();
            pi = pi.pred();

            Symbol fsym = t.getSubterm(pi).getSymbol();
            res = TypeTools.getFunctionArgAt(typeContext.getSingleTypeOf(fsym).getTypeMatrix(), j);
        }

        return res;
    }


    /** Tries to get the type of a variable from the term t
     */
    public static AlgebraTerm getTypeOfVariableInTerm(VariableSymbol vsym, AlgebraTerm t, TypeContext typeContext) {
        Set<VariableSymbol> vars = new LinkedHashSet<VariableSymbol>();
        vars.add(vsym);
        return SimplifierTools.getTypeOfVariablesInTerm(vars, t, typeContext);
    }
}