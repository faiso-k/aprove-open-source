package aprove.verification.dpframework.MCSProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * A single MC transition rule.
 *
 * @author fuhs
 */
public class MCRule implements HasFunctionSymbols, HasVariables, Exportable, Immutable {

    private final TRSFunctionApplication left;
    private final TRSFunctionApplication right;
    private final MCOrderConstraints constraints;

    /**
     * @param left - f(x_1, ..., x_n) for a function symbol f and pairwise
     *  different variables x_1, ..., x_n not occurring in <code>right</code>
     * @param right - g(y_1, ..., y_k) for a function symbol g and pairwise
     *  different variables y_1, ..., y_k not occurring in <code>left</code>
     * @param constraints - all its variables must occur in left or right
     */
    private MCRule(TRSFunctionApplication left, TRSFunctionApplication right, MCOrderConstraints constraints) {
        if (Globals.useAssertions) {
            Set<TRSVariable> lrVars = new LinkedHashSet<TRSVariable>();
            boolean reallyNew;
            for (TRSTerm lArg : left.getArguments()) {
                assert lArg.isVariable();
                reallyNew = lrVars.add((TRSVariable) lArg);
                assert reallyNew;
            }
            for (TRSTerm rArg : right.getArguments()) {
                assert rArg.isVariable();
                reallyNew = lrVars.add((TRSVariable) rArg);
                assert reallyNew;
            }
            Set<TRSVariable> constraintsVars = constraints.getVariables();
            assert lrVars.containsAll(constraintsVars);
        }
        this.left = left;
        this.right = right;
        this.constraints = constraints;
    }

    public static MCRule create(TRSFunctionApplication left, TRSFunctionApplication right, MCOrderConstraints constraints) {
        return new MCRule(left, right, constraints);
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        sb.append(this.left.export(o));
        sb.append(" :- [");
        sb.append(this.constraints.export(o));
        sb.append("] ; ");
        sb.append(this.right.export(o));
        return sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        res.add(this.left.getRootSymbol());
        res.add(this.right.getRootSymbol());
        return res;
    }

    @Override
    public Set<TRSVariable> getVariables() {
        Set<TRSVariable> res = new LinkedHashSet<TRSVariable>();
        this.left.collectVariables(res);
        this.right.collectVariables(res);
        return res;
    }

    /**
     * Adds the ITRS rules corresponding to this to <code>itrsRules</code>.
     * Here
     *    f(X1, ..., Xn) :- constraints ; g(Y1, ..., Yk)
     * is transformed to the two rules
     *    f(X1, ..., Xn) -> cond(constraints, Y1, ..., Yk)
     *    cond(TRUE, Y1, ..., Yk) -> g(Y1, ..., Yk)
     * where 'cond' is a fresh symbol.
     *
     * @param fng - generates new names for new function symbols
     * @param predefMap - for predefined ITRS symbols
     * @param itrsRules - here the new rules corresponding to this
     *  will be added
     */
    public void addITRSRules(FreshNameGenerator fng,
            IDPPredefinedMap predefMap, Collection<GeneralizedRule> itrsRules) {
        FunctionSymbol rRoot = this.right.getRootSymbol();
        int rRootArity = rRoot.getArity();
        List<TRSTerm> rightArgs = this.right.getArguments();

        // new name for the condition symbol
        String condSymName = fng.getFreshName(rRoot.getName(), false);
        int condSymArity = 1 + rRootArity;
        FunctionSymbol condSym =
            FunctionSymbol.create(condSymName, condSymArity);

        // construct first new rule ...
        ArrayList<TRSTerm> firstNewRightArgs = new ArrayList<TRSTerm>(condSymArity);
        firstNewRightArgs.add(this.constraints.toITRSConjunction(predefMap));
        firstNewRightArgs.addAll(rightArgs);
        TRSTerm firstNewRight =
            TRSTerm.createFunctionApplication(condSym, firstNewRightArgs);
        firstNewRightArgs = null;
        GeneralizedRule firstNewRule = GeneralizedRule.create(this.left, firstNewRight);

        // ... and the second one
        ArrayList<TRSTerm> secondNewLeftArgs = new ArrayList<TRSTerm>(condSymArity);
        secondNewLeftArgs.add(predefMap.getBooleanTrue().getTerm());
        secondNewLeftArgs.addAll(rightArgs);
        TRSFunctionApplication newLeft =
            TRSTerm.createFunctionApplication(condSym, secondNewLeftArgs);
        secondNewLeftArgs = null;
        GeneralizedRule secondNewRule = GeneralizedRule.create(newLeft, this.right);

        // ... and finally add them
        itrsRules.add(firstNewRule);
        itrsRules.add(secondNewRule);
    }

    /**
     * @return the left
     */
    public TRSFunctionApplication getLeft() {
        return this.left;
    }

    /**
     * @return the right
     */
    public TRSFunctionApplication getRight() {
        return this.right;
    }

    /**
     * @return the constraints
     */
    public MCOrderConstraints getConstraints() {
        return this.constraints;
    }
}
