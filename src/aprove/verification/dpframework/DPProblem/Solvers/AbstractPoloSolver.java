/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * @author cotto
 * @param <C> The type of the coefficients used in the constraints' polynomials.
 */
public abstract class AbstractPoloSolver<C extends GPolyCoeff> {
    /**
     * Generate the constraints while taking care of the given StrictMode.
     * @param pConstraints The constraints resulting from the rules in P.
     * @param usableRulesConstraint The constraints resulting from the rules.
     * @param strictMode The strict mode (SEARCHSTRICT etc.).
     * @param interpretation The interpretation.
     * @param coeffFactory A factory used to build the coefficients.
     * @param orderPolyFactory A factory used to build the polynomials.
     * @param constraintFactory A factory used to build the constraints.
     * @return the generated constraints.
     */
    public OrderPolyConstraint<C> generateConstraints(
            final Set<Constraint<TRSTerm>> pConstraints,
            final OrderPolyConstraint<C> usableRulesConstraint,
            final StrictMode strictMode,
            final GInterpretation<C> interpretation,
            final GPolyFactory<C, GPolyVar> coeffFactory,
            final OrderPolyFactory<C> orderPolyFactory,
            final ConstraintFactory<C> constraintFactory,
            Abortion aborter) throws AbortionException {
        // create the OrderPolyConstraints for the pairs depending on the used
        // mode
        Set<OrderPolyConstraint<C>> orderPolyConstraints = this.generateWithStrictModeConstraints(
                pConstraints, strictMode, interpretation, coeffFactory,
                orderPolyFactory, constraintFactory, aborter);

        OrderPolyConstraint<C> newConstraint =
            constraintFactory.createAnd(orderPolyConstraints);
        newConstraint =
            constraintFactory.createAnd(usableRulesConstraint, newConstraint);
        newConstraint =
            constraintFactory.createQuantifierE(
                    newConstraint, newConstraint.getFreeVariables());
        return newConstraint;
    }

    /**
     * Generate {@link OrderPolyConstraint}s for a set of Term constraints
     * while taking care of the giving StrictModeS
     * @param pConstraints The constraints resulting from the rules in P.
     * @param usableRulesConstraint The constraints resulting from the rules.
     * @param strictMode The strict mode (SEARCHSTRICT etc.).
     * @param interpretation The interpretation.
     * @param coeffFactory A factory used to build the coefficients.
     * @param orderPolyFactory A factory used to build the polynomials.
     * @param constraintFactory A factory used to build the constraints.
     * @return the generated constraints.
     */
    public Set<OrderPolyConstraint<C>> generateWithStrictModeConstraints(
            final Set<Constraint<TRSTerm>> pConstraints,
            final StrictMode strictMode,
            final GInterpretation<C> interpretation,
            final GPolyFactory<C, GPolyVar> coeffFactory,
            final OrderPolyFactory<C> orderPolyFactory,
            final ConstraintFactory<C> constraintFactory,
            Abortion aborter) throws AbortionException {
        Set<OrderPolyConstraint<C>> orderPolyConstraints =
            new LinkedHashSet<OrderPolyConstraint<C>>(
                    pConstraints.size());
        if (strictMode.equals(StrictMode.AUTOSTRICT)) {
            // replace the constraints in pConstraints with constraints
            // where "- s_i" is added. Also add the constraint "sum(s_i) > 0".
            Map<Constraint<TRSTerm>, GPolyVar> modifiedConstraints =
                new LinkedHashMap<Constraint<TRSTerm>, GPolyVar>(pConstraints.size());
            Set<GPolyVar> vars = new LinkedHashSet<GPolyVar>(pConstraints.size());
            GPoly<C, GPolyVar> newConstraint =
                coeffFactory.zero();
            for (Constraint<TRSTerm> constraint : pConstraints) {
                aborter.checkAbortion();
                GPolyVar newVar =
                    GAtomicVar.createVariable("autostrict_" + vars.size());
                vars.add(newVar);
                modifiedConstraints.put(constraint, newVar);
                // sum up the new variables
                newConstraint =
                    coeffFactory.plus(coeffFactory.buildFromVariable(newVar),
                            newConstraint);
            }
            orderPolyConstraints.addAll(
                    interpretation.fromTermConstraints(modifiedConstraints, aborter));
            // the sum of all new variables must be > 0.
            OrderPoly<C> newConstraintPoly =
                orderPolyFactory.buildFromCoeff(newConstraint);
            orderPolyConstraints.add(
                    constraintFactory.createWithQuantifier(
                            newConstraintPoly, ConstraintType.GT));
        } else if (strictMode.equals(StrictMode.AUTOSTRICTJAR)
                || strictMode.equals(StrictMode.SEARCHSTRICT)) {
            // for AUTOSTRICTJAR and SEARCHSTRICT:
            // remember all const(l) - const(r) for every pair in P
            Set<GPoly<C, GPolyVar>> constDiffs =
                new LinkedHashSet<GPoly<C, GPolyVar>>(
                        pConstraints.size());
            // get the order polynomials and the constant parts of the polys.
            Map<OrderPolyConstraint<C>, GPoly<C, GPolyVar>>
                newOrderPolyConstraints =
                interpretation.fromTermConstraintsWithConstants(pConstraints, aborter);
            for (Map.Entry<OrderPolyConstraint<C>, GPoly<C, GPolyVar>> entry
                    : newOrderPolyConstraints.entrySet()) {
                aborter.checkAbortion();
                // add l - r >= 0
                orderPolyConstraints.add(entry.getKey());
                constDiffs.add(entry.getValue());
            }
            OrderPolyConstraint<C> newOPC;
            if (strictMode.equals(StrictMode.AUTOSTRICTJAR)) {
                // add the constraint sum(constant) > 0.
                OrderPoly<C> orderPoly =
                    orderPolyFactory.buildFromCoeff(
                        coeffFactory.plus(constDiffs));
                newOPC = constraintFactory.createWithQuantifier(
                        orderPoly, ConstraintType.GT);
            } else {
                // add l-r >= 0 and NOT(AND(l-r = 0))
                Set<OrderPolyConstraint<C>> notEqConstraints =
                    new LinkedHashSet<OrderPolyConstraint<C>>(
                            constDiffs.size());
                Set<OrderPolyConstraint<C>> geConstraints =
                    new LinkedHashSet<OrderPolyConstraint<C>>(
                            constDiffs.size());
                for (GPoly<C, GPolyVar> diff : constDiffs) {
                    aborter.checkAbortion();
                    OrderPoly<C> orderPoly =
                        orderPolyFactory.buildFromCoeff(diff);
                    OrderPolyConstraint<C> constraintEq =
                        new OPCAtom<C>(
                                orderPoly, null, ConstraintType.EQ);
                    OrderPolyConstraint<C> constraintGe =
                        new OPCAtom<C>(
                                orderPoly, null, ConstraintType.GE);
                    notEqConstraints.add(constraintEq);
                    geConstraints.add(constraintGe);
                }
                newOPC = constraintFactory.createAnd(notEqConstraints);
                newOPC = constraintFactory.createNot(newOPC);
                OrderPolyConstraint<C> temp =
                    constraintFactory.createAnd(geConstraints);
                newOPC = constraintFactory.createAnd(temp, newOPC);
            }
            orderPolyConstraints.add(newOPC);
        } else if (strictMode.equals(StrictMode.ALLSTRICT)) {
            aborter.checkAbortion();
            orderPolyConstraints.addAll(
                    interpretation.fromTermConstraints(pConstraints, aborter));
        }
        return orderPolyConstraints;
    }
}
