package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.math.BigInteger;
import java.util.LinkedHashSet;
import java.util.Optional;
import java.util.Set;

import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Applies simplifications to free variables in the guard/rhs, e.g.
 *   f(z) -> f(x)   :|: z = x+1 && x >= 0
 * is simplified to
 *   f(z) -> f(z-1) :|: z-1 >= 0
 *
 * @author mnaaf
 *
 */
public abstract class EqualityPropagation {

    //Tries to solve lhs = rhs for the only variable in lhs
    private static Optional<TRSTerm> trySolveEq(TRSTerm lhs, TRSTerm rhs) {
        if (lhs.getVariables().size() != 1) {
            return Optional.empty();
        }
        TRSVariable var = lhs.getVariables().iterator().next();
        if (rhs.hasSubterm(var)) {
            return Optional.empty();
        }

        SimplePolynomial poly;
        try {
            poly = CpxIntTermHelper.toSimplePolynomial(lhs);
        } catch (NotRepresentableAsPolynomialException e) {
            return Optional.empty();
        }

        if (poly.getDegree() != 1) {
            return Optional.empty();
        }

        BigInteger bigcoeff = poly.getSimpleMonomials().get(IndefinitePart.create(var.getName(), 1));
        if (!bigcoeff.abs().equals(BigInteger.ONE)) {
            return Optional.empty();
        }

        BigInteger delta = bigcoeff.multiply(poly.getNumericalAddend());
        if (delta.equals(BigInteger.ZERO)) {
            return Optional.of(rhs);
        }
        SimplePolynomial deltaPoly = SimplePolynomial.create(delta);
        return Optional.of(TRSTerm.createFunctionApplication(CpxIntTermHelper.fSub, rhs, deltaPoly.toTerm()));
    }

    //(heuristically) removes equalities that define free variables from the constraints, moving them into the rhs
    public static RntsRule apply(RntsRule rule) {
        Set<TRSVariable> lhsVars = rule.getLeft().getVariables();
        boolean modified = true;
        while (modified) {
            modified = false;
            Constraint remove = null;
            TRSSubstitution subs = null;

            for (Constraint cond : rule.getConstraints()) {
                if (cond.getConstraintTerm().isVariable()) continue;
                TRSFunctionApplication funapp = (TRSFunctionApplication)cond.getConstraintTerm();
                FunctionSymbol fun = funapp.getRootSymbol();
                if (fun.equals(CpxIntTermHelper.fEq)) {
                    TRSTerm lhs = funapp.getArgument(0);
                    TRSTerm rhs = funapp.getArgument(1);

                    //simple heuristic: only consider z = x+n for integer n, free var x, bounded var z
                    if (lhs.isVariable() && lhsVars.contains((TRSVariable)lhs)) {
                        Set<TRSVariable> vars = rhs.getVariables();
                        if (vars.size() != 1) continue;
                        TRSVariable var = vars.iterator().next();
                        if (lhsVars.contains(var)) continue;
                        Optional<TRSTerm> solved = trySolveEq(rhs, lhs);
                        if (solved.isPresent()) {
                            remove = cond;
                            subs = TRSSubstitution.create(vars.iterator().next(),solved.get());
                            break;
                        }
                    }
                }
            }

            if (remove != null) {
                modified = true;
                Set<Constraint> newGuard = new LinkedHashSet<>();
                newGuard.addAll(rule.getConstraints());
                newGuard.remove(remove);
                try {
                    rule = RntsRule.createUnsafe(
                            rule.getLeft(), rule.getRight(), rule.getCost(),
                            ImmutableCreator.create(newGuard))
                            .applyIntegerSubstitution(subs);
                } catch (NotRepresentableAsPolynomialException e) {
                    throw new RuntimeException(e); //internal error
                }
            }
        }
        return rule;
    }

}
