package aprove.verification.oldframework.IntegerReasoning;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Incomplete but fast implication checker for a conjunction of integer relations and an integer relation to check.
 * @author cryingshadow
 * @version $Id$
 */
public class HeuristicImplicationChecker {

    /**
     * @param relations A set of relations encoding their conjunction.
     * @param relation Some relation.
     * @param creator
     * @return YES if the specified relation is implied by the conjunction. NO if its negation is implied. MAYBE if
     *         neither holds or our check is too weak.
     * @throws DivisionByZeroException
     */
    public static YNM checkImplication(
        IntegerRelationSet relations,
        IntegerRelation relation,
        FunctionalIntegerExpressionCreator creator
    ) throws DivisionByZeroException {
        // first check whether the relation or its negation are contained
        if (relations.contains(relation)) {
            return YNM.YES;
        }
        if (relations.contains(relation.negate())) {
            return YNM.NO;
        }
        FunctionalIntegerExpression lhs = HeuristicImplicationChecker.normalize(relation.getLhs(), creator);
        FunctionalIntegerExpression rhs = HeuristicImplicationChecker.normalize(relation.getRhs(), creator);
        UnionFind<FunctionalIntegerExpression> equalTerms = new UnionFind<FunctionalIntegerExpression>();
        equalTerms.union(HeuristicImplicationChecker.getCommutativeVariants(lhs, creator));
        equalTerms.union(HeuristicImplicationChecker.getCommutativeVariants(rhs, creator));
        for (IntegerRelation rel : relations.getEquations()) {
            Set<FunctionalIntegerExpression> variants =
                new LinkedHashSet<FunctionalIntegerExpression>(
                    HeuristicImplicationChecker.getCommutativeVariants(
                        HeuristicImplicationChecker.normalize(rel.getLhs(), creator),
                        creator
                    )
                );
            variants.addAll(
                HeuristicImplicationChecker.getCommutativeVariants(
                    HeuristicImplicationChecker.normalize(rel.getRhs(), creator),
                    creator
                )
            );
            equalTerms.union(variants);
        }
        HeuristicImplicationChecker.updateVariablesToRepresentatives(equalTerms);
        FunctionalIntegerExpression repLhs = equalTerms.find(lhs);
        FunctionalIntegerExpression repRhs = equalTerms.find(rhs);
        switch (relation.getRelationType()) {
            case NE:
                if (repLhs == repRhs) {
                    return YNM.NO;
                }
                if (HeuristicImplicationChecker.checkUnequal(relations, repLhs, repRhs, equalTerms)) {
                    return YNM.YES;
                }
                if (
                    HeuristicImplicationChecker.checkLE(
                        relations,
                        new PlainIntegerOperation(ArithmeticOperationType.ADD, repLhs, PlainIntegerConstant.ONE),
                        repRhs,
                        equalTerms,
                        creator
                    ) == YNM.YES
                ) {
                    return YNM.YES;
                }
                if (
                    HeuristicImplicationChecker.checkLE(
                        relations,
                        new PlainIntegerOperation(ArithmeticOperationType.ADD, repRhs, PlainIntegerConstant.ONE),
                        repLhs,
                        equalTerms,
                        creator
                    ) == YNM.YES
                ) {
                    return YNM.YES;
                }
                return YNM.MAYBE;
            case EQ:
                if (repLhs == repRhs) {
                    return YNM.YES;
                }
                if (HeuristicImplicationChecker.checkUnequal(relations, repLhs, repRhs, equalTerms)) {
                    return YNM.NO;
                }
                if (
                    HeuristicImplicationChecker.checkLE(relations, repLhs, repRhs, equalTerms, creator) == YNM.YES
                    && HeuristicImplicationChecker.checkLE(relations, repRhs, repLhs, equalTerms, creator) == YNM.YES
                ) {
                    return YNM.YES;
                }
                return YNM.MAYBE;
            case LT:
                return
                    HeuristicImplicationChecker.checkLE(
                        relations,
                        new PlainIntegerOperation(ArithmeticOperationType.ADD, repLhs, PlainIntegerConstant.ONE),
                        repRhs,
                        equalTerms,
                        creator
                    );
            case GT:
                return
                    HeuristicImplicationChecker.checkLE(
                        relations,
                        new PlainIntegerOperation(ArithmeticOperationType.ADD, repRhs, PlainIntegerConstant.ONE),
                        repLhs,
                        equalTerms,
                        creator
                    );
            case GE:
                return HeuristicImplicationChecker.checkLE(relations, repRhs, repLhs, equalTerms, creator);
            default:
                if (Globals.useAssertions) {
                    assert relation.getRelationType() == IntegerRelationType.LE :
                        "Someone found a new way to relate integers!";
                }
        }
        return HeuristicImplicationChecker.checkLE(relations, repLhs, repRhs, equalTerms, creator);
    }

    /**
     * Adds all combinations of left- and right-hand sides with the specified operation to the set res.
     * @param operation Some binary operation.
     * @param variants1 Terms as left-hand sides.
     * @param variants2 Terms as right-hand sides.
     * @param res Some set of terms.
     * @param creator For creating expressions.
     */
    private static void addAllCombinations(
        ArithmeticOperationType operation,
        Set<FunctionalIntegerExpression> variants1,
        Set<FunctionalIntegerExpression> variants2,
        Set<FunctionalIntegerExpression> res,
        FunctionalIntegerExpressionCreator creator
    ) {
        for (FunctionalIntegerExpression arg1 : variants1) {
            for (FunctionalIntegerExpression arg2 : variants2) {
                res.add(creator.operation(operation, arg1, arg2));
            }
        }
    }

    /**
     * @param relations A set of relations representing their conjunction.
     * @param lhs The left-hand side of an LE relation.
     * @param rhs The right-hand side of an LE relation.
     * @param equalTerms
     * @param creator
     * @return YES if the specified LE relation is implied by the conjunction. NO if its negation is implied. MAYBE if
     *         neither holds or our check is too weak. The answer NO is actually just there to quickly abort the search
     *         if NO is already proven. We do not explicitly look for NO answers if this is costly.
     * @throws DivisionByZeroException
     */
    private static YNM checkLE(
        IntegerRelationSet relations,
        FunctionalIntegerExpression lhs,
        FunctionalIntegerExpression rhs,
        UnionFind<FunctionalIntegerExpression> equalTerms,
        FunctionalIntegerExpressionCreator creator
    ) throws DivisionByZeroException {
        // first check whether we are there already
        final LinearIntegerExpression lhsLinear = HeuristicImplicationChecker.toLinear(lhs, creator);
        final LinearIntegerExpression rhsLinear = HeuristicImplicationChecker.toLinear(rhs, creator);
        if (lhsLinear.y == null) {
            if (rhsLinear.y == null) {
                if (lhsLinear.z.compareTo(rhsLinear.z) <= 0) {
                    return YNM.YES;
                } else {
                    return YNM.NO;
                }
            }
        } else if (
            lhsLinear.y.equals(rhsLinear.y)
            && lhsLinear.x.compareTo(rhsLinear.x) <= 0
            && lhsLinear.z.compareTo(rhsLinear.z) <= 0
        ) {
            return YNM.YES;
        }
        // now filter out relations that cannot contribute to the result
        final Set<IntegerRelation> rels = HeuristicImplicationChecker.filter(relations, lhs, rhs);
        // bidirectional search - the maps encode expressions plus constant offsets in or against LE direction
        final Map<FunctionalIntegerExpression, Set<ConstantPair>> yes =
            new LinkedHashMap<FunctionalIntegerExpression, Set<ConstantPair>>();
        final Map<FunctionalIntegerExpression, Set<ConstantPair>> no =
            new LinkedHashMap<FunctionalIntegerExpression, Set<ConstantPair>>();
        Set<ConstantPair> yesSet = new LinkedHashSet<ConstantPair>();
        yesSet.add(new ConstantPair(lhsLinear.x, lhsLinear.z));
        Set<ConstantPair> noSet = new LinkedHashSet<ConstantPair>();
        noSet.add(new ConstantPair(lhsLinear.x, lhsLinear.z.subtract(BigInteger.ONE)));
        yes.put(lhsLinear.y, yesSet);
        no.put(lhsLinear.y, noSet);
        final ConstantPair rhsPair = new ConstantPair(rhsLinear.x, rhsLinear.z);
        while (HeuristicImplicationChecker.updateKnowledge(rels, yes, no, equalTerms)) {
            if (yes.containsKey(rhsLinear.y)) {
                for (ConstantPair otherPair : yes.get(rhsLinear.y)) {
                    Integer compare = otherPair.compareTo(rhsPair);
                    if (compare != null && compare <= 0) {
                        return YNM.YES;
                    }
                }
            }
            if (no.containsKey(rhsLinear.y)) {
                for (ConstantPair otherPair : yes.get(rhsLinear.y)) {
                    Integer compare = otherPair.compareTo(rhsPair);
                    if (compare != null && compare >= 0) {
                        return YNM.NO;
                    }
                }
            }
        }
        return YNM.MAYBE;
    }

    /**
     * @param relations The relations.
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @param equalTerms Equal terms.
     * @return True if we can prove lhs != rhs. False otherwise.
     */
    private static boolean checkUnequal(
        IntegerRelationSet relations,
        FunctionalIntegerExpression lhs,
        FunctionalIntegerExpression rhs,
        UnionFind<FunctionalIntegerExpression> equalTerms
    ) {
        for (FunctionalIntegerExpression left : equalTerms.getPartition(lhs)) {
            for (FunctionalIntegerExpression right : equalTerms.getPartition(rhs)) {
                for (IntegerRelation rel : relations.getUndirectedInequalities()) {
                    FunctionalIntegerExpression relLhs = rel.getLhs();
                    FunctionalIntegerExpression relRhs = rel.getRhs();
                    if (
                        (left.equals(relLhs) && right.equals(relRhs)) || (left.equals(relRhs) && right.equals(relLhs))
                    ) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * @param relations A set of relations.
     * @param lhs Some expression.
     * @param rhs Another expression.
     * @return A subset of the specified relations such that only those relations are retained which are no equations
     *         and can contribute to a decision whether lhs <= rhs holds.
     */
    private static Set<IntegerRelation> filter(
        IntegerRelationSet relations,
        FunctionalIntegerExpression lhs,
        FunctionalIntegerExpression rhs
    ) {
        Set<IntegerRelation> candidates = new LinkedHashSet<IntegerRelation>(relations);
        Set<IntegerVariable> used = new LinkedHashSet<IntegerVariable>();
        used.addAll(lhs.getVariables());
        Set<IntegerRelation> res = new LinkedHashSet<IntegerRelation>();
        boolean change;
        do {
            change = false;
            Iterator<IntegerRelation> it = candidates.iterator();
            while (it.hasNext()) {
                IntegerRelation rel = it.next();
                if (rel.isEquation() || rel.isUndirectedInequality()) {
                    continue;
                }
                Set<? extends IntegerVariable> vars = rel.getVariables();
                if (Collections.disjoint(used, vars)) {
                    continue;
                }
                res.add(rel);
                used.addAll(vars);
                it.remove();
                change = true;
            }
        } while (change);
        if (used.containsAll(rhs.getVariables())) {
            return res;
        }
        return Collections.emptySet();
    }

    /**
     * @param exp Some expression.
     * @param creator Creator for expressions.
     * @return A set of equal expressions to the specified one (including the specified one) by commutativity.
     */
    private static Set<FunctionalIntegerExpression> getCommutativeVariants(
        FunctionalIntegerExpression exp,
        FunctionalIntegerExpressionCreator creator
    ) {
        if (!(exp instanceof CompoundFunctionalIntegerExpression)) {
            return Collections.singleton(exp);
        }
        CompoundFunctionalIntegerExpression term = (CompoundFunctionalIntegerExpression)exp;
        Set<FunctionalIntegerExpression> res = new LinkedHashSet<FunctionalIntegerExpression>();
        switch (term.getArity()) {
            case 1:
                for (
                    FunctionalIntegerExpression arg :
                        HeuristicImplicationChecker.getCommutativeVariants(term.getArguments().get(0), creator)
                ) {
                    res.add(creator.operation(term.getOperation(), arg));
                }
                break;
            case 2:
                Set<FunctionalIntegerExpression> variants1 =
                    new LinkedHashSet<FunctionalIntegerExpression>(
                        HeuristicImplicationChecker.getCommutativeVariants(term.getArguments().get(0), creator)
                    );
                Set<FunctionalIntegerExpression> variants2 =
                    new LinkedHashSet<FunctionalIntegerExpression>(
                        HeuristicImplicationChecker.getCommutativeVariants(term.getArguments().get(1), creator)
                    );
                final ArithmeticOperationType op = term.getOperation();
                HeuristicImplicationChecker.addAllCombinations(op, variants1, variants2, res, creator);
                if (op.isCommutative()) {
                    HeuristicImplicationChecker.addAllCombinations(op, variants2, variants1, res, creator);
                }
                break;
            default:
                return Collections.singleton(exp);
        }
        return res;
    }

    /**
     * @param c Some constant.
     * @param exp Some linear expression a * x + b.
     * @return The linear expression (c * a) * x + (c * b).
     */
    private static LinearIntegerExpression multiplicationWithConstantToLinear(
        BigInteger c,
        LinearIntegerExpression exp
    ) {
        if (exp.y == null) {
            return new LinearIntegerExpression(BigInteger.ONE, null, c.multiply(exp.z));
        } else if (c.compareTo(BigInteger.ZERO) == 0) {
            return new LinearIntegerExpression(BigInteger.ONE, null, BigInteger.ZERO);
        } else if (c.compareTo(BigInteger.ONE) == 0) {
            return exp;
        } else {
            return new LinearIntegerExpression(c.multiply(exp.x), exp.y, c.multiply(exp.z));
        }
    }

    /**
     * @param term Some integer term.
     * @param creator Creator for expressions.
     * @return The specified term in a normalized form.
     * @throws DivisionByZeroException If the specified term contains a division by zero.
     */
    private static FunctionalIntegerExpression normalize(
        FunctionalIntegerExpression term,
        FunctionalIntegerExpressionCreator creator
    ) throws DivisionByZeroException {
        return HeuristicImplicationChecker.toLinear(term, creator).toIntegerTerm(creator);
    }

    /**
     * TODO use this code for heuristic terms (at least in part)?
     * @param exp Some term.
     * @param creator Creator for expressions.
     * @return The linear variant of the specified term.
     * @throws DivisionByZeroException
     */
    private static LinearIntegerExpression toLinear(
        FunctionalIntegerExpression exp,
        FunctionalIntegerExpressionCreator creator
    ) throws DivisionByZeroException {
        if (exp instanceof IntegerVariable) {
            return new LinearIntegerExpression(BigInteger.ONE, exp, BigInteger.ZERO);
        }
        if (exp instanceof IntegerConstant) {
            return new LinearIntegerExpression(BigInteger.ONE, null, ((IntegerConstant)exp).getIntegerValue());
        }
        CompoundFunctionalIntegerExpression term = (CompoundFunctionalIntegerExpression)exp;
        switch (term.getOperation()) {
            case ADD:
                return
                    HeuristicImplicationChecker.toLinearAdditive(
                        HeuristicImplicationChecker.toLinear(term.getArguments().get(0), creator),
                        HeuristicImplicationChecker.toLinear(term.getArguments().get(1), creator),
                        creator
                    );
            case SUB:
                return
                    HeuristicImplicationChecker.toLinearAdditive(
                        HeuristicImplicationChecker.toLinear(term.getArguments().get(0), creator),
                        HeuristicImplicationChecker.toLinear(term.getArguments().get(1).negate(), creator),
                        creator
                    );
            case MUL: {
                LinearIntegerExpression left =
                    HeuristicImplicationChecker.toLinear(term.getArguments().get(0), creator);
                LinearIntegerExpression right =
                    HeuristicImplicationChecker.toLinear(term.getArguments().get(1), creator);
                if (left.y == null) {
                    return HeuristicImplicationChecker.multiplicationWithConstantToLinear(left.z, right);
                } else if (right.y == null) {
                    return HeuristicImplicationChecker.multiplicationWithConstantToLinear(right.z, left);
                } else if (left.z.compareTo(BigInteger.ZERO) == 0 && right.z.compareTo(BigInteger.ZERO) == 0) {
                    // left.x * left.y * right.x * right.y
                    return
                        new LinearIntegerExpression(
                            left.x.multiply(right.x),
                            creator.operation(ArithmeticOperationType.MUL, left.y, right.y),
                            BigInteger.ZERO
                        );
                } else {
                    // (left.x * left.y + left.z) * (right.x * right.y + right.z)
                    // thus, left.x * left.y * right.x * right.y + left.x * left.y * right.z
                    // + left.z * right.x * right.y + left.z * right.z
                    // probably too complicated for us
                    return new LinearIntegerExpression(BigInteger.ONE, exp, BigInteger.ZERO);
                }
            }
            case NEG: {
                LinearIntegerExpression neg = HeuristicImplicationChecker.toLinear(term.getArguments().get(0), creator);
                return new LinearIntegerExpression(neg.x.negate(), neg.y, neg.z.negate());
            }
            case TIDIV: {
                LinearIntegerExpression left =
                    HeuristicImplicationChecker.toLinear(term.getArguments().get(0), creator);
                LinearIntegerExpression right =
                    HeuristicImplicationChecker.toLinear(term.getArguments().get(1), creator);
                if (right.y == null) {
                    if (right.z.compareTo(BigInteger.ZERO) == 0) {
                        throw new DivisionByZeroException();
                    }
                    if (right.z.compareTo(BigInteger.ONE) == 0) {
                        return left;
                    } else if (
                        left.z.remainder(right.z).compareTo(BigInteger.ZERO) == 0
                        && (left.y == null || left.x.remainder(right.z).compareTo(BigInteger.ZERO) == 0)
                    ) {
                        return
                            new LinearIntegerExpression(
                                left.y == null ? null : left.x.divide(right.z),
                                left.y,
                                left.z.divide(right.z)
                            );
                    }
                }
                // probably too complicated for us - fall through
            }
            default:
                return new LinearIntegerExpression(BigInteger.ONE, exp, BigInteger.ZERO);
        }
    }

    /**
     * @param left The linear left-hand side.
     * @param right The linear right-hand side.
     * @param creator Creator for expressions.
     * @return The linear expression for left + right.
     */
    private static LinearIntegerExpression toLinearAdditive(
        LinearIntegerExpression left,
        LinearIntegerExpression right,
        FunctionalIntegerExpressionCreator creator
    ) {
        final FunctionalIntegerExpression resExpr;
        final BigInteger multiplier;
        if (left.y == null) {
            resExpr = right.y;
            multiplier = right.x;
        } else if (right.x == null) {
            resExpr = left.y;
            multiplier = left.x;
        } else if (left.x.compareTo(BigInteger.ONE) == 0) {
            if (right.x.compareTo(BigInteger.ONE) == 0) {
                resExpr = creator.operation(ArithmeticOperationType.ADD, left.y, right.y);
                multiplier = BigInteger.ONE;
            } else {
                // we have: left.y + left.z + right.x * right.y + right.z
                // thus: (left.y + right.x * right.y) + (left.z + right.z)
                resExpr =
                    creator.operation(
                        ArithmeticOperationType.ADD,
                        left.y,
                        creator.operation(
                            ArithmeticOperationType.MUL,
                            creator.constant(right.x),
                            right.y
                        )
                    );
                multiplier = BigInteger.ONE;
            }
        } else if (right.x.compareTo(BigInteger.ONE) == 0) {
            // we have: left.x * left.y + left.z + right.y + right.z
            // thus: (left.x * left.y + right.y) + (left.z + right.z)
            resExpr =
                creator.operation(
                    ArithmeticOperationType.ADD,
                    creator.operation(
                        ArithmeticOperationType.MUL,
                        creator.constant(left.x),
                        left.y
                    ),
                    right.y
                );
            multiplier = BigInteger.ONE;
        } else if (left.x.compareTo(right.x) == 0) {
            // we have: left.x * left.y + left.z + left.x * right.y + right.z
            // thus: left.x * (left.y + right.y) + (left.z + right.z)
            resExpr = creator.operation(ArithmeticOperationType.ADD, left.y, right.y);
            multiplier = left.x;
        } else {
            // we have: left.x * left.y + left.z + right.x * right.y + right.z
            // thus: (left.x * left.y + right.x * right.y) + (left.z + right.z)
            resExpr =
                creator.operation(
                    ArithmeticOperationType.ADD,
                    creator.operation(
                        ArithmeticOperationType.MUL,
                        creator.constant(left.x),
                        left.y
                    ),
                    creator.operation(
                        ArithmeticOperationType.MUL,
                        creator.constant(right.x),
                        right.y
                    )
                );
            multiplier = BigInteger.ONE;
        }
        return new LinearIntegerExpression(multiplier, resExpr, left.z.add(right.z));
    }

    private static boolean updateKnowledge(
        Set<IntegerRelation> rels,
        Map<FunctionalIntegerExpression, Set<ConstantPair>> yes,
        Map<FunctionalIntegerExpression, Set<ConstantPair>> no,
        UnionFind<FunctionalIntegerExpression> equalTerms
    ) {
        // TODO Auto-generated method stub
        return false;
    }

    /**
     * Updates the variables in the specified union-find structure to their representatives.
     * @param equalTerms The equal terms.
     */
    private static void updateVariablesToRepresentatives(final UnionFind<FunctionalIntegerExpression> equalTerms) {
        final Substitution updater =
            new Substitution() {

                @Override
                public Expression substitute(Variable v) {
                    return equalTerms.find((IntegerVariable)v);
                }

            };
        final Set<Set<FunctionalIntegerExpression>> newEquals = new LinkedHashSet<Set<FunctionalIntegerExpression>>();
        for (ImmutableSet<FunctionalIntegerExpression> partition : equalTerms.getPartitions()) {
            Set<FunctionalIntegerExpression> newPartition = new LinkedHashSet<FunctionalIntegerExpression>(partition);
            for (FunctionalIntegerExpression exp : partition) {
                newPartition.add((FunctionalIntegerExpression)exp.applySubstitution(updater));
            }
            newEquals.add(newPartition);
        }
        for (Set<FunctionalIntegerExpression> partition : newEquals) {
            equalTerms.union(partition);
        }
    }

    /**
     * A pair (x,y) of a multiplicative constant factor x and an additive constant offset y.
     * @author cryingshadow
     * @version $Id$
     */
    private static class ConstantPair extends Pair<BigInteger, BigInteger> {

        /**
         * For serialization.
         */
        private static final long serialVersionUID = 7297678673436052101L;

        /**
         * @param factor The multiplicative constant factor.
         * @param offset The additive constant offset.
         */
        public ConstantPair(BigInteger factor, BigInteger offset) {
            super(factor, offset);
        }

        /**
         * @param o Some other ConstantPair.
         * @return 0 if both pairs are equal. Some value greater than zero if for all integer values i it holds that
         *         this.x * i + this.y > o.x * i + o.y. If the latter holds for < instead of >, it returns a negative
         *         value. Null otherwise.
         */
        public Integer compareTo(ConstantPair o) {
            final int factor = this.x.compareTo(o.x);
            if (factor == 0) {
                return this.y.compareTo(o.y);
            } else if (factor < 0) {
                if (this.y.compareTo(o.y) < 0) {
                    return -1;
                }
            } else {
                if (this.y.compareTo(o.y) > 0) {
                    return 1;
                }
            }
            return null;
        }

    }

    /**
     * A triple (x,y,z) encoding the term x * y + z for two constants x and z and some non-constant expression y.
     * @author cryingshadow
     * @version $Id$
     */
    private static class LinearIntegerExpression extends Triple<BigInteger, FunctionalIntegerExpression, BigInteger> {

        /**
         * @param factor The multiplicative constant factor.
         * @param exp The non-constant expression.
         * @param offset The additive constant offset.
         */
        public LinearIntegerExpression(BigInteger factor, FunctionalIntegerExpression exp, BigInteger offset) {
            super(factor, exp, offset);
        }

        /**
         * @param creator Creator for expressions.
         * @return The integer term represented by this linear expression.
         */
        public FunctionalIntegerExpression toIntegerTerm(FunctionalIntegerExpressionCreator creator) {
            if (this.y == null) {
                return creator.constant(this.z);
            }
            if (this.x.compareTo(BigInteger.ONE) == 0) {
                if (this.z.compareTo(BigInteger.ZERO) == 0) {
                    return this.y;
                }
                return creator.operation(ArithmeticOperationType.ADD, this.y, creator.constant(this.z));
            }
            if (this.z.compareTo(BigInteger.ZERO) == 0) {
                return creator.operation(ArithmeticOperationType.MUL, creator.constant(this.x), this.y);
            }
            return
                creator.operation(
                    ArithmeticOperationType.ADD,
                    creator.operation(ArithmeticOperationType.MUL, creator.constant(this.x), this.y),
                    creator.constant(this.z)
                );
        }

    }

}
