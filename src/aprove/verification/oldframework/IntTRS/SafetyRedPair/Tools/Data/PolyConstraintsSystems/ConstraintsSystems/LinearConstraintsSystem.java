package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Linear constraints system, PolyConstraintsSystem restricted to linear polynomials.
 * @author marinag, cryingshadow
 */
public class LinearConstraintsSystem extends PolyConstraintsSystem {

    public static final LinearConstraintsSystem LIN_TRUE = LinearConstraintsSystem.create();

    /**
     * @return empty linear constraint
     */
    public static LinearConstraintsSystem create() {
        return LinearConstraintsSystem.create(new HashSet<SimplePolyConstraint>());
    }

    public static LinearConstraintsSystem create(final Collection<SimplePolyConstraint> constraints) {
        for (final SimplePolyConstraint c : constraints) {
            assert c.getPolynomial().isLinear() : "Non-linear constraints are not welcome here";
        }
        return new LinearConstraintsSystem(constraints);
    }

    /**
     * @param consSys polynomial constraints system
     * @return linear constraints system using the constraints of consSys
     */
    public static LinearConstraintsSystem create(final PolyConstraintsSystem consSys) {
        return LinearConstraintsSystem.create(consSys.constraints);
    }

    /**
     * @param constraint polynomial constraint
     * @return linear constraints system with a single constraint
     */
    public static LinearConstraintsSystem create(final SimplePolyConstraint constraint) {
        final HashSet<SimplePolyConstraint> constraints = new HashSet<>();
        constraints.add(constraint);
        return LinearConstraintsSystem.create(constraints);
    }

    public static LinearConstraintsSystem merge(final PolyConstraintsSystem a, final PolyConstraintsSystem b) {
        return LinearConstraintsSystem.create(PolyConstraintsSystem.merge(a, b));
    }

    public static SimplePolynomial replace(SimplePolynomial poly, HashMap<String, IndefinitePart> reverseMap) {
        SimplePolynomial result = SimplePolynomial.ZERO;
        for (final Entry<IndefinitePart, BigInteger> indef : poly.getSimpleMonomials().entrySet()) {
            result = result.plus(LinearConstraintsSystem.replace(indef.getKey(), reverseMap).times(indef.getValue()));
        }
        return result;
    }

    private static SimplePolynomial replace(IndefinitePart indef, HashMap<String, IndefinitePart> reverseMap) {
        SimplePolynomial result = SimplePolynomial.ONE;
        for (final Entry<String, Integer> exp : indef.getExponents().entrySet()) {
            final String variable = exp.getKey();
            if (reverseMap.containsKey(variable)) {
                result =
                    result.times(
                        SimplePolynomial.create(reverseMap.get(variable), BigInteger.ONE).power(exp.getValue())
                    );
            } else {
                result = result.times(IndefinitePart.create(exp.getKey(), exp.getValue()));
            }
        }
        return result;
    }

    private static SimplePolyConstraint replace(
        SimplePolyConstraint constraint,
        HashMap<String, IndefinitePart> reverseMap
    ) {
        return
            new SimplePolyConstraint(
                LinearConstraintsSystem.replace(constraint.getPolynomial(), reverseMap),
                constraint.getType()
            );
    }

    /**
     * Create system with the constraints from a
     * @param a - collection of constraints
     */
    public LinearConstraintsSystem(final Collection<SimplePolyConstraint> constraints) {
        super(PolyConstraintsSystem.create(constraints).constraints);
    }

    @Override
    public LinearConstraintsSystem addConstraint(final SimplePolyConstraint c) {
        return LinearConstraintsSystem.create(super.addConstraint(c));
    }

    //    @Override
    //    public LinearConstraintsSystem addAllConstraints(final Collection<SimplePolyConstraint> c) {
    //        return create(super.addAllConstraints(c));
    //    }
    //
    //    /**
    //     * The constraints turn into the variables, each variable gets a constraint (not including the numerical addend)
    //     * @param numericalAddend - values for numerical addend
    //     * @param constraintType - constraint type
    //     * @param lowerBounds - lower bounds (if exist)
    //     * @param upperBounds - upper bounds (if exist)
    //     * @return transposed system
    //     */
    //    public LinearConstraintsSystem transpose(
    //        final HashMap<IndefinitePart, BigInteger> numericalAddend,
    //        final ConstraintType constraintType,
    //        final HashMap<Integer, BigInteger> lowerBounds,
    //        final HashMap<Integer, BigInteger> upperBounds)
    //    {
    //
    //        final HashSet<SimplePolyConstraint> result = new HashSet<>();
    //
    //        for (final String id : this.getIdefinities()) {
    //
    //            final ArrayList<SimplePolynomial> polySet = new ArrayList<>();
    //
    //            int i = 0;
    //            for (int c = 0; c < this.constraints.size(); c++) {
    //
    //                final BigInteger n = this.get(c).getPolynomial().getSimpleMonomials().get(IndefinitePart.create(id, 1));
    //                if (n != null && !n.equals(BigInteger.ZERO)) {
    //                    final SimplePolynomial poly = SimplePolynomial.create(constraintIdentifier(i)).times(n.negate());
    //                    polySet.add(poly);
    //                }
    //                i++;
    //            }
    //
    //            final IndefinitePart indef = IndefinitePart.create(id, 1);
    //            if (numericalAddend != null && numericalAddend.containsKey(indef)) {
    //                polySet.add(SimplePolynomial.create(numericalAddend.get(indef)));
    //            }
    //
    //
    //            result.add(new SimplePolyConstraint(SimplePolynomial.plus(polySet), constraintType));
    //        }
    //
    //
    //        for (int j = 0; j < this.constraints.size(); j++) {
    //            if (lowerBounds != null && lowerBounds.containsKey(j)) {
    //                result.add(this.getVariableConstraint(
    //                    constraintIdentifier(j),
    //                    BigInteger.ONE,
    //                    lowerBounds.get(j).negate(),
    //                    ConstraintType.GE));
    //            }
    //
    //            if (upperBounds != null && upperBounds.containsKey(j)) {
    //                result.add(this.getVariableConstraint(
    //                    constraintIdentifier(j),
    //                    BigInteger.ONE.negate(),
    //                    upperBounds.get(j),
    //                    ConstraintType.GE));
    //            }
    //        }
    //
    //        return new LinearConstraintsSystem(result);
    //    }
    //
    //    /**
    //     * Create polynomial out of the numerical addend, the constraints turn into variables
    //     * @return polynomial with the addend values as coefficients
    //     */
    //    public SimplePolynomial transposeAddend() {
    //        final HashSet<SimplePolynomial> polySet = new HashSet<>();
    //
    //        int i = 0;
    //        for (final SimplePolyConstraint c : this.constraints) {
    //
    //            final BigInteger n = c.getPolynomial().getNumericalAddend();
    //
    //            final SimplePolynomial poly = SimplePolynomial.create(constraintIdentifier(i)).times(n);
    //            polySet.add(poly);
    //            i++;
    //        }
    //
    //        return SimplePolynomial.plus(polySet);
    //    }
    //
    //    /**
    //     * Get constraints, all variables are non negative
    //     */
    //    public HashSet<SimplePolyConstraint> getAllVariablesNonNegativeConstraints() {
    //        final HashSet<SimplePolyConstraint> result = new HashSet<>();
    //
    //        for (final String id : this.getIdefinities()) {
    //            result.add(getVariableNonNegativeConstraint(id));
    //        }
    //
    //        return result;
    //    }
    //
    //    /**
    //     * Add constraint: id >= 0
    //     * @param id - variable name
    //     */
    //    public SimplePolyConstraint getVariableNonNegativeConstraint(final String id) {
    //        return getVariableConstraint(id, BigInteger.ONE, BigInteger.ZERO, ConstraintType.GE);
    //    }
    //
    //    /**
    //     * get constraint: id x factor + addend (== , >=)
    //     *
    //     * @param id - variable name
    //     * @param factor - factor
    //     * @param addend - addend
    //     * @param constraintType - constraint type
    //     * @return
    //     */
    //    public SimplePolyConstraint getVariableConstraint(
    //        final String id,
    //        final BigInteger factor,
    //        final BigInteger addend,
    //        final ConstraintType constraintType)
    //    {
    //        return new SimplePolyConstraint(
    //            SimplePolynomial.create(id).times(factor).plus(SimplePolynomial.create(addend)),
    //            constraintType);
    //    }
    //
    @Override
    public Object clone() {
        return LinearConstraintsSystem.create(this.constraints);
    }

    public HashMap<String, HashSet<SimplePolyConstraint>> getLowBoundedVars() {
        final HashMap<String, HashSet<SimplePolyConstraint>> result = new HashMap<>();
        for (SimplePolyConstraint cons : this.constraints) {
            if (!cons.getPolynomial().isLinear()) {
                continue;
            }
            if (cons.getType().equals(ConstraintType.EQ)) {
                for (final String var : cons.getPolynomial().getVariables()) {
                    if (!result.containsKey(var)) {
                        result.put(var, new HashSet<SimplePolyConstraint>());
                    }
                    result.get(var).add(cons);
                }
            } else {
                for (Entry<IndefinitePart, BigInteger> indefP : cons.getPolynomial().getSimpleMonomials().entrySet()) {
                    for (Entry<String, Integer> expP : indefP.getKey().getExponents().entrySet()) {
                        if (indefP.getValue().compareTo(BigInteger.ZERO) > 0) {
                            final String var = expP.getKey();
                            if (!result.containsKey(var)) {
                                result.put(var, new HashSet<SimplePolyConstraint>());
                            }
                            result.get(var).add(cons);
                        }
                    }
                }
            }
        }
        return result;
    }

    public HashMap<String, HashSet<SimplePolyConstraint>> getUpBoundedVars() {
        final HashMap<String, HashSet<SimplePolyConstraint>> result = new HashMap<>();
        for (final SimplePolyConstraint cons : this.constraints) {
            if (!cons.getPolynomial().isLinear()) {
                continue;
            }
            if (cons.getType().equals(ConstraintType.EQ)) {
                for (final String var : cons.getPolynomial().getVariables()) {
                    if (!result.containsKey(var)) {
                        result.put(var, new HashSet<SimplePolyConstraint>());
                    }
                    result.get(var).add(cons);
                }
            } else {
                for (Entry<IndefinitePart, BigInteger> indefP : cons.getPolynomial().getSimpleMonomials().entrySet()) {
                    for (Entry<String, Integer> expP : indefP.getKey().getExponents().entrySet()) {
                        if (indefP.getValue().compareTo(BigInteger.ZERO) < 0) {
                            final String var = expP.getKey();
                            if (!result.containsKey(var)) {
                                result.put(var, new HashSet<SimplePolyConstraint>());
                            }
                            result.get(var).add(cons);
                        }
                    }
                }
            }
        }
        return result;
    }

    @Override
    public LinearConstraintsSystem merge(final PolyConstraintsSystem a) {
        return LinearConstraintsSystem.merge(this, a);
    }

    public PolyConstraintsSystem replaceIndefinite(final HashMap<String, IndefinitePart> reverseMap) {
        final HashMap<String, SimplePolynomial> map = new HashMap<>();
        for (final Entry<String, IndefinitePart> var : reverseMap.entrySet()) {
            map.put(var.getKey(), SimplePolynomial.create(var.getValue(), BigInteger.ONE));
        }
        final HashSet<SimplePolyConstraint> constraints = new HashSet<>();
        for (final SimplePolyConstraint c : this.getConstraints()) {
            constraints.add(LinearConstraintsSystem.replace(c, reverseMap));
        }
        return PolyConstraintsSystem.create(constraints);
    }

    @Override
    public LinearConstraintsSystem toGeConstraintsSystem() {
        final ArrayList<SimplePolyConstraint> newConstraints = new ArrayList<>();
        for (final SimplePolyConstraint c : this.constraints) {
            if (c.getType().equals(ConstraintType.EQ)) {
                final SimplePolynomial poly = c.getPolynomial();
                newConstraints.add(new SimplePolyConstraint(poly, ConstraintType.GE));
                newConstraints.add(new SimplePolyConstraint(poly.negate(), ConstraintType.GE));
            } else {
                newConstraints.add(c);
            }
        }
        return LinearConstraintsSystem.create(newConstraints);
    }

}
