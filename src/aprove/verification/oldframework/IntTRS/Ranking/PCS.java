package aprove.verification.oldframework.IntTRS.Ranking;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.RankingRedPair.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Represents a system of polynomial constraints (GEConstraints). Here the
 * constraint are stored in form of a list. I won't create unnecessary copies of
 * lists, so be careful.
 * @author Matthias Hoelzel
 */
public class PCS implements Exportable {
    /** List of constraints. */
    private final List<GEConstraint> constraints;

    /** Some aborter */
    private final Abortion aborter;

    /**
     * Constructor!
     * @param geConstraints list of constraints, non-null
     * @param ab some aborter
     */
    public PCS(final List<GEConstraint> geConstraints, final Abortion ab) {
        if (geConstraints == null) {
            throw new UnsupportedOperationException("List must not be null.");
        }

        this.aborter = ab;
        this.constraints = geConstraints;
    }

    /**
     * Returns a linear combination of this, i.e. the sum of GEConstraints of
     * this, multiplied by some new coefficient.
     * @param ng some name generator
     * @param prefix use this prefix for the new coefficients
     * @return LinearCombination
     * @throws AbortionException can be aborted
     */
    public LinearCombination toLinearCombination(final FreshNameGenerator ng, final String prefix)
        throws AbortionException
    {
        VarPolynomial poly1 = VarPolynomial.ZERO;
        SimplePolynomial poly2 = SimplePolynomial.ZERO;

        for (final GEConstraint geCon : this.getConstraints()) {
            this.aborter.checkAbortion();
            final String newCoefficientName = ng.getFreshName("l", false);
            final VarPolynomial newCoefficient = VarPolynomial.createCoefficient(newCoefficientName);
            final SimplePolynomial newCoefficientAsSimplePoly = SimplePolynomial.create(newCoefficientName);
            poly1 = poly1.plus(geCon.getPoly().times(newCoefficient));
            poly2 = poly2.plus(newCoefficientAsSimplePoly.times(SimplePolynomial.create(geCon.getConstant())));
        }

        return new LinearCombination(poly1, poly2);
    }

    /**
     * Eliminates all variables, that are not in toKeep contained.
     * @param toKeep set of variables
     * @return PCS
     * @throws AbortionException can be aborted
     */
    public PCS eliminateOtherVariables(final LinkedHashSet<String> toKeep) throws AbortionException {
        PCS result = this;
        for (final String occVar : this.getVariables()) {
            this.aborter.checkAbortion();
            if (!toKeep.contains(occVar)) {
                result = result.eliminateVariable(occVar);
            }
        }
        return result;
    }

    /**
     * Return the set of all variables, occurring in this.
     * @return set of strings
     */
    public Set<String> getVariables() {
        final LinkedHashSet<String> variables = new LinkedHashSet<>();
        for (final GEConstraint c : this.constraints) {
            variables.addAll(c.getVariables());
        }
        return variables;
    }

    /**
     * Eliminates a given variable and returns a new polynomial constraint
     * system. This method will only work if this is a linear constraint system.
     * Otherwise this method will just do nothing.
     * @param toEliminate variable to be eliminated
     * @return PCS
     */
    public PCS eliminateVariable(final String toEliminate) {
        if (!this.isLinear()) {
            return this;
        } else {
            final LinkedList<GEConstraint> resultConstraints = new LinkedList<>();
            final LinkedList<VarPolynomial> lowerBoundPolys = new LinkedList<>();
            final LinkedList<VarPolynomial> upperBoundPolys = new LinkedList<>();

            // Which are upper & which are lower bounds?
            for (final GEConstraint c : this.constraints) {
                final VarPolynomial diffPoly = c.getDiffPoly();

                if (diffPoly.getVariables().contains(toEliminate)) {
                    final BigInteger coeff = diffPoly.getCoefficientPoly(toEliminate).getNumericalAddend();
                    if (coeff.compareTo(BigInteger.ZERO) > 0) {
                        lowerBoundPolys.add(diffPoly);
                    } else {
                        upperBoundPolys.add(diffPoly);
                    }
                } else {
                    resultConstraints.add(c);
                }
            }

            // Use every possible combination.
            if (!(lowerBoundPolys.isEmpty() || upperBoundPolys.isEmpty())) {
                for (final VarPolynomial lowerBoundPoly : lowerBoundPolys) {
                    final SimplePolynomial lowerCoeffPoly = lowerBoundPoly.getCoefficientPoly(toEliminate);
                    final BigInteger lowerCoeffAbs = lowerCoeffPoly.getNumericalAddend().abs();
                    for (final VarPolynomial upperBoundPoly : upperBoundPolys) {
                        final SimplePolynomial upperCoeffPoly = upperBoundPoly.getCoefficientPoly(toEliminate);
                        final BigInteger upperCoeffAbs = upperCoeffPoly.getNumericalAddend().abs();

                        final BigInteger lcm =
                            lowerCoeffAbs.multiply(upperCoeffAbs).divide(lowerCoeffAbs.gcd(upperCoeffAbs));

                        final VarPolynomial newPolyConstraint =
                            lowerBoundPoly.times(VarPolynomial.create(lcm.divide(lowerCoeffAbs))).plus(
                                upperBoundPoly.times(VarPolynomial.create(lcm.divide(upperCoeffAbs))));
                        final GEConstraint newConstraint = GEConstraint.create(newPolyConstraint, BigInteger.ZERO);

                        resultConstraints.add(newConstraint);
                    }
                }
            }

            return new PCS(resultConstraints, this.aborter);
        }
    }

    /**
     * Returns true iff only linear arithmetic occurs.
     * @return boolean
     */
    public boolean isLinear() {
        for (final GEConstraint c : this.constraints) {
            if (!c.isLinear()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Removes all constraints that are trivial like 0 >= 0.
     * @return PCS
     */
    private PCS removeTrivialConstraints() {
        final int size = this.constraints.size();
        final LinkedHashSet<GEConstraint> newConstraints = new LinkedHashSet<>(size);
        for (final GEConstraint c : this.constraints) {
            if (!c.isTrivial()) {
                newConstraints.add(c);
            }
        }
        if (size == newConstraints.size()) {
            return this;
        } else {
            return new PCS(new LinkedList<>(newConstraints), this.aborter);
        }
    }

    /**
     * Removes trivial constraints like 0 >= 0 and deletes other unneeded stuff.
     * @return PCS
     */
    public PCS cleanUp() {
        final PCS current = this.removeTrivialConstraints();
        final List<GEConstraint> constraintList = current.getConstraints();
        final int size = constraintList.size();
        final LinkedHashMap<VarPolynomial, BigInteger> boundMap = new LinkedHashMap<>(size);
        final LinkedHashMap<VarPolynomial, GEConstraint> constraintMap = new LinkedHashMap<>(size);
        for (final GEConstraint c : constraintList) {
            boolean addConstraint = true;
            if (boundMap.containsKey(c.getPoly())) {
                addConstraint = boundMap.get(c.getPoly()).compareTo(c.getConstant()) < 0;
            }

            if (addConstraint) {
                boundMap.put(c.getPoly(), c.getConstant());
                constraintMap.put(c.getPoly(), c);
            }
        }

        return new PCS(new LinkedList<>(constraintMap.values()), this.aborter);
    }

    /**
     * Returns a linear combination of this, i.e. the sum of GEConstraints of
     * this, multiplied by some new coefficient.
     * @param ng some name generator
     * @return LinearCombination
     */
    public LinearCombination toLinearCombination(final FreshNameGenerator ng) throws AbortionException {
        return this.toLinearCombination(ng, "c");
    }

    /**
     * Getter for the constraints.
     * @return List of GEConstraint
     */
    public List<GEConstraint> getConstraints() {
        return this.constraints;
    }

    /**
     * Checks whether or not the conjunction of the constraints implies toCheck.
     * May return a false negative answer.
     * @param toCheck GEConstraint
     * @return boolean
     * @throws AbortionException can be aborted
     */
    public boolean checkImplicationDestructive(final GEConstraint toCheck) throws AbortionException {
        if (!toCheck.isLinear()) {
            return false;
        }

        final FormulaFactory<SMTLIBTheoryAtom> factory = new FullSharingFactory<>();
        final List<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<>();

        final Formula<SMTLIBTheoryAtom> toCheckNegation =
            factory.buildNot(factory.buildTheoryAtom(toCheck.toSMTLIBRatGE()));
        formulas.add(toCheckNegation);

        for (final GEConstraint constraint : this.constraints) {
            // TODO: Non-linearity?
            if (constraint.isLinear()) {
                formulas.add(factory.buildTheoryAtom(constraint.toSMTLIBRatGE()));
            }
        }

        try {
            final SMTEngine smtEngine = new YicesEngine();
            final YNM ynm = smtEngine.satisfiable(formulas, SMTLogic.QF_LRA, this.aborter);

            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger l = DebugLogger.getLogger("ranking");
                l.log("Does the ");
                l.logln(this);
                l.logln("imply " + toCheck + "?");
                l.logln(ynm.equals(YNM.NO));
            }

            return ynm.equals(YNM.NO);
        } catch (final WrongLogicException e) {
            return false;
        }
    }

    /**
     * Returns the constraints in form of SMT-constraints.
     * @param onlyLinearConstraints true if you want to rule out nonlinear
     * constraints
     * @return list of SMTLIBRatGEs
     */
    public List<SMTLIBRatGE> toSMT(final boolean onlyLinearConstraints) {
        final List<SMTLIBRatGE> result = new LinkedList<>();
        for (final GEConstraint constraint : this.constraints) {
            if (onlyLinearConstraints && !constraint.isLinear()) {
                continue;
            }
            result.add(constraint.toSMTLIBRatGE());
        }
        return result;
    }

    /**
     * Checks whether or not the conjunction of the constraints implies toCheck.
     * May return a false negative answer.
     * @param toCheck GEConstraint
     * @return boolean
     */
    public boolean checkImplicationConstructive(final GEConstraint toCheck) {
        // TODO: Implement me!
        return false;
    }

    @Override
    public int hashCode() {
        int result = 0;
        for (final GEConstraint constraint : this.constraints) {
            result += constraint.hashCode();
        }
        return result;
    }

    @Override
    public boolean equals(final Object other) {
        if (other == null || !(other instanceof PCS)) {
            return false;
        }
        final PCS otherPCS = (PCS) other;
        return this.constraints.containsAll(otherPCS.constraints) && otherPCS.constraints.containsAll(this.constraints);
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("PCS:");
        for (final GEConstraint constraint : this.constraints) {
            sb.append("\n\t");
            sb.append(constraint);
        }
        return sb.toString();
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        final Iterator<GEConstraint> constraintIter = this.constraints.iterator();
        while (constraintIter.hasNext()) {
            sb.append(constraintIter.next().export(eu));
            if (constraintIter.hasNext()) {
                sb.append(eu.andSign());
                sb.append(eu.linebreak());
            }
        }
        return eu.indent(sb.toString());
    }
}
