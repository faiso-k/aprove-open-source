package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;

import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Replaces free variables in a cost polynomial by its (first) upper bound
 * in the guard, e.g.:
 *   f(x) -{ y }-> f(x)   :|: y <= x^2
 * is simplified (over-approximated) to
 *   f(z) -{ x^2 }> f(z-1) :|: y <= x^2
 * The constraint is kept, as there might be other constraints involving y,
 * e.g. z <= y && y <= x^2.
 *
 * Note: only handles constraints "y <= poly" and is only applicable if the
 * cost does not contain negative coefficients!
 *
 * @author mnaaf
 */
public abstract class CostSimplification {

    // returns the first upper bound for var, i.e. a constraint of the form "var <= poly"
    private static Optional<SimplePolynomial> getUpperbound(TRSVariable var, Set<Constraint> guard) {
        for (Constraint c : guard) {
            if (c.getConstraintTerm().isVariable()) continue;
            TRSFunctionApplication funapp = (TRSFunctionApplication)c.getConstraintTerm();
            FunctionSymbol fun = funapp.getRootSymbol();

            if (fun.equals(CpxIntTermHelper.fLe)) {
                TRSTerm lhs = funapp.getArgument(0);
                TRSTerm rhs = funapp.getArgument(1);

                //only consider var <= expr
                if (lhs.isVariable() && var.equals((TRSVariable)lhs)) {
                    try {
                        return Optional.of(CpxIntTermHelper.toSimplePolynomial(rhs));
                    } catch (NotRepresentableAsPolynomialException e) {
                        // just ignore non polynomial bounds
                    }
                }
            }
        }
        return Optional.empty();
    }

    private static boolean hasNegativeCoeff(SimplePolynomial poly) {
        for (Entry<IndefinitePart,BigInteger> m : poly.getSimpleMonomials().entrySet()) {
            if (m.getValue().signum() != 1) {
                return true;
            }
        }
        return false;
    }

    private static SimplePolynomial simplifyCost(SimplePolynomial cost, Set<Constraint> guard, Set<TRSVariable> lhsVars) {
        // negative coefficients are not supported
        if (hasNegativeCoeff(cost)) {
            return cost;
        }

        // check all free variables and replace them if possible
        Map<String,SimplePolynomial> subsMap = new LinkedHashMap<>();
        for (String varname : cost.getVariables()) {
            TRSVariable var = TRSTerm.createVariable(varname);
            if (lhsVars.contains(var)) continue;

            Optional<SimplePolynomial> upperbound = getUpperbound(var, guard);
            if (upperbound.isPresent()) {
                subsMap.put(varname, upperbound.get());
            }
        }
        return cost.substitute(subsMap);
    }

    // replace free variables by their upper bounds (from the guard)
    public static RntsRule apply(RntsRule rule) {
        SimplePolynomial newCost = simplifyCost(rule.getCost(), rule.getConstraints(), rule.getLeft().getVariables());
        return RntsRule.createUnsafe(rule.getLeft(), rule.getRight(), newCost, rule.getConstraints());
    }

    public static CpxRntsProblem apply(CpxRntsProblem rnts) {
        Set<RntsRule> newRules = new LinkedHashSet<>();
        for (RntsRule rule : rnts.getRules()) {
            newRules.add(apply(rule));
        }
        return rnts.cloneWithNewRules(ImmutableCreator.create(newRules));
    }

}
