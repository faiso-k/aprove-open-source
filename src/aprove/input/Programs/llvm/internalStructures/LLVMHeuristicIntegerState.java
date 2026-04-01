package aprove.input.Programs.llvm.internalStructures;

import java.io.*;
import java.math.*;
import java.util.*;

import org.json.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractBoundedInt.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;
import aprove.verification.oldframework.SMT.Solver.Z3.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * Integer state for heuristic LLVM states.
 * TODO check for inequalities whether they match an allocation bound => change to LT then? This should already be
 *      clear since we must have <= and >= relations to the bounds...
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMHeuristicIntegerState extends LLVMIntegerState {

    /**
     * Solver factory for dumping SMT queries.
     */
    private static final Z3ExtSolverFactory dumperFactory = new Z3ExtSolverFactory();

    /**
     * @param first Some constant.
     * @param ty A relation type.
     * @param second Some other constant.
     * @return True if the specified relation holds. False otherwise.
     */
    public static boolean checkRelationOnConstants(BigInteger first, LLVMHeuristicRelationType ty, BigInteger second) {
        switch (ty) {
            case NE:
                return first.compareTo(second) != 0;
            case EQ:
                return first.compareTo(second) == 0;
            case LE:
                return first.compareTo(second) <= 0;
            case LT:
                return first.compareTo(second) < 0;
        }
        throw new IllegalStateException("Unknown relation type detected!");
    }

    /**
     * @param relations A set of relations.
     * @return An encoding of all constant distances between two variables known by the specified relations in two
     *         versions: once as a map from references to sets of pairs of references and constants (here, a mapping
     *         ref1 -> {(ref2,c),...} means ref1 = ref2 + c) and once as a map from constants to sets of pairs of
     *         references (here, a mapping c -> {(ref1,ref2),...} means ref1 = ref2 + c).
     */
    public static Pair<LLVMOffsetMap, LLVMCommonOffsetMap> computeOffsetMaps(Set<LLVMHeuristicRelation> relations) {
        // entries x -> (y, c) represent the knowledge x = y + c
        LLVMOffsetMap offsetMap = new LLVMOffsetMap();
        // entries c -> (x, y) represent the knowledge x = y + c
        LLVMCommonOffsetMap commonOffsetMap = new LLVMCommonOffsetMap();
        for (LLVMHeuristicRelation rel : relations) {
            if (!rel.isEquation()) {
                continue;
            }
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
            if (
                !(
                    lhsLinear.x instanceof LLVMHeuristicVarRef
                    && rhsLinear.x instanceof LLVMHeuristicVarRef
                    && lhsLinear.z.compareTo(BigInteger.ONE) == 0
                    && rhsLinear.z.compareTo(BigInteger.ONE) == 0
                )
            ) {
                continue;
            }
            LLVMHeuristicVariable leftRef = (LLVMHeuristicVariable)lhsLinear.x;
            LLVMHeuristicVariable rightRef = (LLVMHeuristicVariable)rhsLinear.x;
            if (!offsetMap.containsKey(leftRef)) {
                offsetMap.put(leftRef, new LinkedHashSet<Pair<LLVMHeuristicVariable, BigInteger>>());
            }
            if (!offsetMap.containsKey(rightRef)) {
                offsetMap.put(rightRef, new LinkedHashSet<Pair<LLVMHeuristicVariable, BigInteger>>());
            }
            Set<Pair<LLVMHeuristicVariable, BigInteger>> leftSet = offsetMap.get(leftRef);
            Set<Pair<LLVMHeuristicVariable, BigInteger>> rightSet = offsetMap.get(rightRef);
            Set<Pair<LLVMHeuristicVariable, BigInteger>> leftToAdd = new LinkedHashSet<Pair<LLVMHeuristicVariable, BigInteger>>();
            Set<Pair<LLVMHeuristicVariable, BigInteger>> rightToAdd = new LinkedHashSet<Pair<LLVMHeuristicVariable, BigInteger>>();
            // leftRef = rightRef + leftRightOffset
            BigInteger leftRightOffset = rhsLinear.y.subtract(lhsLinear.y);
            // rightRef = leftRef + rightLeftOffset
            BigInteger rightLeftOffset = lhsLinear.y.subtract(rhsLinear.y);
            if (!commonOffsetMap.containsKey(leftRightOffset)) {
                commonOffsetMap.put(leftRightOffset, new LinkedHashSet<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>());
            }
            if (!commonOffsetMap.containsKey(rightLeftOffset)) {
                commonOffsetMap.put(rightLeftOffset, new LinkedHashSet<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>());
            }
            commonOffsetMap.get(leftRightOffset).add(new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(leftRef, rightRef));
            commonOffsetMap.get(rightLeftOffset).add(new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(rightRef, leftRef));
            for (Pair<LLVMHeuristicVariable, BigInteger> pair : leftSet) {
                // leftRef = pair.x + pair.y
                // => rightRef + leftRightOffset = pair.x + pair.y
                BigInteger rightPairOffset = pair.y.subtract(leftRightOffset);
                BigInteger pairRightOffset = leftRightOffset.subtract(pair.y);
                if (!commonOffsetMap.containsKey(rightPairOffset)) {
                    commonOffsetMap.put(rightPairOffset, new LinkedHashSet<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>());
                }
                if (!commonOffsetMap.containsKey(pairRightOffset)) {
                    commonOffsetMap.put(pairRightOffset, new LinkedHashSet<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>());
                }
                rightToAdd.add(new Pair<LLVMHeuristicVariable, BigInteger>(pair.x, rightPairOffset));
                commonOffsetMap.get(rightPairOffset).add(new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(rightRef, pair.x));
                offsetMap.get(pair.x).add(new Pair<LLVMHeuristicVariable, BigInteger>(rightRef, pairRightOffset));
                commonOffsetMap.get(pairRightOffset).add(new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(pair.x, rightRef));
            }
            for (Pair<LLVMHeuristicVariable, BigInteger> pair : rightSet) {
                // rightRef = pair.x + pair.y
                // => leftRef + rightLeftOffset = pair.x + pair.y
                BigInteger leftPairOffset = pair.y.subtract(rightLeftOffset);
                BigInteger pairLeftOffset = rightLeftOffset.subtract(pair.y);
                if (!commonOffsetMap.containsKey(leftPairOffset)) {
                    commonOffsetMap.put(leftPairOffset, new LinkedHashSet<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>());
                }
                if (!commonOffsetMap.containsKey(pairLeftOffset)) {
                    commonOffsetMap.put(pairLeftOffset, new LinkedHashSet<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>());
                }
                leftToAdd.add(new Pair<LLVMHeuristicVariable, BigInteger>(pair.x, pair.y.subtract(rightLeftOffset)));
                commonOffsetMap.get(leftPairOffset).add(new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(leftRef, pair.x));
                offsetMap.get(
                    pair.x
                ).add(new Pair<LLVMHeuristicVariable, BigInteger>(leftRef, rightLeftOffset.subtract(pair.y)));
                commonOffsetMap.get(pairLeftOffset).add(new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(pair.x, leftRef));
            }
            leftSet.add(new Pair<LLVMHeuristicVariable, BigInteger>(rightRef, leftRightOffset));
            leftSet.addAll(leftToAdd);
            rightSet.add(new Pair<LLVMHeuristicVariable, BigInteger>(leftRef, rightLeftOffset));
            rightSet.addAll(rightToAdd);
        }
        return new Pair<LLVMOffsetMap, LLVMCommonOffsetMap>(offsetMap, commonOffsetMap);
    }

    /**
     * @param valueMap The values for the references.
     * @return an SMT expression that encodes all information about integer values known in <code>state</code>
     */
    public static SMTExpression<SBool> integerBoundInformationToSMTExp(
        ImmutableMap<LLVMHeuristicVariable, LLVMValue> valueMap
    ) {
        List<SMTExpression<SBool>> subformulas = new LinkedList<>();
        for (Map.Entry<LLVMHeuristicVariable, LLVMValue> e : valueMap.entrySet()) {
            LLVMHeuristicVariable ref = e.getKey();
            AbstractInt value = e.getValue().getThisAsAbstractInt();
            SMTExpression<SInt> refExp = ref.toSMTExp();
            if (value instanceof LiteralInt) {
                subformulas.add(Core.equivalent(refExp, ((LiteralInt) value).toSMTExp()));
            } else if (value instanceof IntervalInt) {
                AbstractInt absIntValue = value;
                IntervalBound lowBound = absIntValue.getLower();
                if (lowBound.isFinite()) {
                    subformulas.add(Ints.greaterEqual(refExp, Ints.constant(lowBound.getConstant())));
                }
                IntervalBound upperBound = absIntValue.getUpper();
                if (upperBound.isFinite()) {
                    subformulas.add(Ints.lessEqual(refExp, Ints.constant(upperBound.getConstant())));
                }
                // IntervalInts are not "just" intervals of integers,
                // the number 0 has a special treatment
                if (
                    !absIntValue.containsLiteral(BigInteger.ZERO)
                    && lowBound.isNegative()
                    && upperBound.isPositive()
                ) {
                    subformulas.add(Core.not(Core.equivalent(refExp, Ints.constant(0))));
                }
            }
        }
        return Core.and(subformulas);
    }

    /**
     * @param int1 The first BigInteger.
     * @param int2 The second BigInteger
     * @param strict Strict relation?
     * @param greater Greater relation?
     * @return int1 (strict ? (greater ? > : <) : (greater ? >= : <=)) int2
     */
    public static boolean isInRelation(
        BigInteger int1,
        BigInteger int2,
        boolean strict,
        boolean greater
    ) {
        if (strict) {
            if (greater) {
                return int1.compareTo(int2) > 0;
            } else {
                return int1.compareTo(int2) < 0;
            }
        } else {
            if (greater) {
                return int1.compareTo(int2) >= 0;
            } else {
                return int1.compareTo(int2) <= 0;
            }
        }
    }

    /**
     * We have a relation of the form resRef = resOp + value or resRef = value + resOp. We are checking whether resRef
     * is in relation with resOp (the kind of relation is specified by the boolean flags greater and strict).
     * @param value A value working as a bridge between resRef and resOp.
     * @param strict Are we looking for a strict or weak relation?
     * @param greater Are we looking for a greater or less than relation?
     * @return True if we can infer that resRef is in the desired relation with resOp. False otherwise.
     */
    public static boolean isInRelationByAddition(AbstractBoundedInt value, boolean strict, boolean greater) {
        return
            (
                greater
                && (
                    (
                        !strict
                        && value.isNonNegative()
                    ) || (
                        strict
                        && value.isPositive()
                    )
                )
            ) || (
                !greater
                && (
                    (
                        !strict
                        && value.isNonPositive()
                    ) || (
                        strict
                        && value.isNegative()
                    )
                )
            );
    }

    /**
     * We have a relation of the form resRef = resOp * value or resRef = value * resOp. We are checking whether resRef
     * is in relation with resOp (the kind of relation is specified by the boolean flags greater and strict).
     * @param value A value working as a bridge between resRef and resOp.
     * @param strict Are we looking for a strict or weak relation?
     * @param greater Are we looking for a greater or less than relation?
     * @return True if we can infer that resRef is in the desired relation with resOp. False otherwise.
     */
    public static boolean isInRelationByMultiplication(AbstractBoundedInt value, boolean strict, boolean greater) {
        return
            (
                greater
                && (
                    (
                        !strict
                        && value.isPositive()
                    ) || (
                        strict
                        && value.isBiggerOne()
                    )
                )
            ) || (
                !greater
                && (
                    (
                        !strict
                        && value.isNegative()
                    ) || (
                        strict
                        && value.isSmallerMinusOne()
                    )
                )
            );
    }

    /**
     * We have a relation of the form resRef = resOp - value. We are checking whether resRef is in relation with resOp
     * (the kind of relation is specified by the boolean flags greater and strict).
     * @param value A value working as a bridge between resRef and resOp.
     * @param strict Are we looking for a strict or weak relation?
     * @param greater Are we looking for a greater or less than relation?
     * @return True if we can infer that resRef is in the desired relation with resOp. False otherwise.
     */
    public static boolean isInRelationBySubtraction(AbstractBoundedInt value, boolean strict, boolean greater) {
        return
            (
                greater
                && (
                    (
                        !strict
                        && value.isNonPositive()
                    ) || (
                        strict
                        && value.isNegative()
                    )
                )
            ) || (
                !greater
                && (
                    (
                        !strict
                        && value.isNonNegative()
                    ) || (
                        strict
                        && value.isPositive()
                    )
                )
            );
    }

    /**
     * @param expr Some expression.
     * @param arrayPatterns A set of array patterns if the useful relations adhere to array patterns. Null otherwise.
     * @return True if arrayPatterns is null or the specified expression is no array expression or adheres to one of
     *         the specified patterns. False otherwise.
     */
    private static boolean adheresToArrayPatterns(
        LLVMHeuristicTerm expr,
        Set<Pair<LLVMHeuristicVariable, BigInteger>> arrayPatterns
    ) {
        if (arrayPatterns == null) {
            return true;
        }
        if (Globals.useAssertions) {
            assert (!arrayPatterns.isEmpty()) : "Array patterns are not null, but empty!";
        }
        Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean> check =
            LLVMHeuristicIntegerState.checkArrayPattern(expr);
        if (check.y) {
            return false;
        } else if (check.x == null) {
            return true;
        }
        LLVMHeuristicVariable base = check.x.x;
        BigInteger factor = check.x.y;
        for (Pair<LLVMHeuristicVariable, BigInteger> pattern : arrayPatterns) {
            if (pattern.x.equals(base) && pattern.y.compareTo(factor) == 0) {
                return true;
            }
        }
        return false;
    }

    /**
     * @param allocations The allocated memory areas.
     * @param associations The associations.
     * @return A mapping from allocated areas to sets of pointers being associated with them.
     */
    private static Map<LLVMAllocation, Set<LLVMHeuristicVariable>> buildInverseAssociations(
        ImmutableList<LLVMAllocation> allocations,
        ImmutableMap<LLVMHeuristicVariable, Integer> associations
    ) {
        Map<LLVMAllocation, Set<LLVMHeuristicVariable>> res = new LinkedHashMap<LLVMAllocation, Set<LLVMHeuristicVariable>>();
        for (Map.Entry<LLVMHeuristicVariable, Integer> association : associations.entrySet()) {
            LLVMAllocation allocation = allocations.get(association.getValue());
            if (!res.containsKey(allocation)) {
                res.put(allocation, new LinkedHashSet<LLVMHeuristicVariable>());
            }
            res.get(allocation).add(association.getKey());
        }
        return res;
    }

    /**
     * @param expr Some expression.
     * @return A pair of an array pattern and a boolean flag. The former is the base address and the constant factor of
     *         the pattern if the expression adheres to an array pattern (and null otherwise). The latter indicated
     *         whether the specified expression violates adherence to array patterns.
     */
    private static Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean> checkArrayPattern(LLVMHeuristicTerm expr) {
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
        if (exprLinear.x == null) {
            // a constant is ok
            return new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(null, false);
        }
        if (exprLinear.z.abs().compareTo(BigInteger.ONE) != 0) {
            // something with a factor which is not added to a base address violates the array pattern
            return new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(null, true);
        }
        if (!(exprLinear.x instanceof LLVMHeuristicOperation)) {
            // a reference with offset is ok
            return new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(null, false);
        }
        LLVMHeuristicOperation add = (LLVMHeuristicOperation)exprLinear.x;
        if (add.getOperation() != ArithmeticOperationType.ADD) {
            return
                new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(
                    null,
                    LLVMHeuristicIntegerState.containsArrayPatternViolation(add)
                );
        }
        LLVMHeuristicTerm addLhs = add.getLhs();
        LLVMHeuristicTerm addRhs = add.getRhs();
        final LLVMHeuristicVariable base;
        final LLVMHeuristicOperation offset;
        if (addLhs instanceof LLVMHeuristicVariable) {
            base = (LLVMHeuristicVariable)addLhs;
            if (!(addRhs instanceof LLVMHeuristicOperation)) {
                // addition of two references is ok
                return new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(null, false);
            }
            offset = (LLVMHeuristicOperation)addRhs;
        } else if (addRhs instanceof LLVMHeuristicVariable) {
            base = (LLVMHeuristicVariable)addRhs;
            if (!(addLhs instanceof LLVMHeuristicOperation)) {
                // addition of two references is ok
                return new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(null, false);
            }
            offset = (LLVMHeuristicOperation)addLhs;
        } else {
            return
                new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(
                    null,
                    LLVMHeuristicIntegerState.containsArrayPatternViolation(add)
                );
        }
        if (offset.getOperation() != ArithmeticOperationType.MUL) {
            return
                new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(
                    null,
                    LLVMHeuristicIntegerState.containsArrayPatternViolation(offset)
                );
        }
        LLVMHeuristicTerm offLhs = offset.getLhs();
        LLVMHeuristicTerm offRhs = offset.getRhs();
        final BigInteger factor;
        if (offLhs instanceof LLVMHeuristicConstRef) {
            factor = ((LLVMHeuristicConstRef)offLhs).getIntegerValue();
            if (!(offRhs instanceof LLVMHeuristicVariable)) {
                // multiplication of constant and non-reference expression violates array pattern
                return new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(null, true);
            }
        } else if (offRhs instanceof LLVMHeuristicConstRef) {
            factor = ((LLVMHeuristicConstRef)offRhs).getIntegerValue();
            if (!(offLhs instanceof LLVMHeuristicVariable)) {
                // multiplication of constant and non-reference expression violates array pattern
                return new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(null, true);
            }
        } else {
            // multiplication with non-constant expression violates the pattern
            return new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(null, true);
        }
        return
            new Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean>(
                new Pair<LLVMHeuristicVariable, BigInteger>(base, factor),
                false
            );
    }

    /**
     * @param usefulRels The useful relations.
     * @param firstExpr The first expression.
     * @param secondExpr The second expression.
     * @return A set of array patterns if the useful relations and the expressions adhere to array patterns.
     *         Null otherwise.
     */
    private static Set<Pair<LLVMHeuristicVariable, BigInteger>> computeArrayPatterns(
        LLVMHeuristicRelationSet usefulRels,
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicTerm secondExpr
    ) {
        Set<Pair<LLVMHeuristicVariable, BigInteger>> res = new LinkedHashSet<Pair<LLVMHeuristicVariable, BigInteger>>();
        Pair<Pair<LLVMHeuristicVariable, BigInteger>, Boolean> pattern = LLVMHeuristicIntegerState.checkArrayPattern(firstExpr);
        if (pattern.y) {
            return null;
        }
        if (pattern.x != null) {
            res.add(pattern.x);
        }
        pattern = LLVMHeuristicIntegerState.checkArrayPattern(secondExpr);
        if (pattern.y) {
            return null;
        }
        if (pattern.x != null) {
            res.add(pattern.x);
        }
        for (LLVMHeuristicRelation rel : usefulRels) {
            pattern = LLVMHeuristicIntegerState.checkArrayPattern(rel.getLhs());
            if (pattern.y) {
                return null;
            }
            if (pattern.x != null) {
                res.add(pattern.x);
            }
            pattern = LLVMHeuristicIntegerState.checkArrayPattern(rel.getRhs());
            if (pattern.y) {
                return null;
            }
            if (pattern.x != null) {
                res.add(pattern.x);
            }
        }
        if (res.isEmpty()) {
            return null;
        }
        return res;
    }

    /**
     * @param knownRelations The relations to consider.
     * @param allocations The allocations.
     * @param associations The associations.
     * @param associationsInverse Inverse mapping from allocations to references being associated to the corresponding
     *                            allocation.
     * @param firstExpr An expression.
     * @param secondExpr An expression.
     * @return A set of relations which might contribute to the truth value of a relation between the two expressions.
     *         Null if no connection between the two expressions can be found.
     */
    private static LLVMHeuristicRelationSet computeUsefulRels(
        LLVMHeuristicRelationSet knownRelations,
        ImmutableList<LLVMAllocation> allocations,
        Map<LLVMHeuristicVariable, Integer> associations,
        Map<LLVMAllocation, Set<LLVMHeuristicVariable>> associationsInverse,
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicTerm secondExpr
    ) {
        LLVMHeuristicRelationSet usefulRels =
            new LLVMHeuristicRelationSet(knownRelations.getRelationsWithoutUndirectedInequalities());
        // gather those non-constant refs which are somehow related to the expressions we are considering
        Set<LLVMHeuristicVariable> relevantRefsFirst = new LinkedHashSet<LLVMHeuristicVariable>();
        Set<LLVMHeuristicVariable> relevantRefsSecond = new LinkedHashSet<LLVMHeuristicVariable>();
        Set<LLVMHeuristicVariable> newRelevantRefsFirst = new LinkedHashSet<LLVMHeuristicVariable>();
        Set<LLVMHeuristicVariable> newRelevantRefsSecond = new LinkedHashSet<LLVMHeuristicVariable>();
        newRelevantRefsFirst.addAll(firstExpr.getVariables(false));
        newRelevantRefsSecond.addAll(secondExpr.getVariables(false));
        while (!newRelevantRefsFirst.isEmpty() || !newRelevantRefsSecond.isEmpty()) {
            relevantRefsFirst.addAll(newRelevantRefsFirst);
            relevantRefsSecond.addAll(newRelevantRefsSecond);
            if (!Collections.disjoint(relevantRefsFirst, relevantRefsSecond)) {
                relevantRefsFirst.addAll(relevantRefsSecond);
                relevantRefsSecond.addAll(relevantRefsFirst);
            }
            newRelevantRefsFirst.clear();
            newRelevantRefsSecond.clear();
            for (LLVMAllocation allocation : allocations) {
                if (relevantRefsFirst.contains(allocation.x)) {
                    newRelevantRefsFirst.add((LLVMHeuristicVariable)allocation.y);
                    if (associationsInverse.containsKey(allocation)) {
                        newRelevantRefsFirst.addAll(associationsInverse.get(allocation));
                    }
                } else if (relevantRefsFirst.contains(allocation.y)) {
                    newRelevantRefsFirst.add((LLVMHeuristicVariable)allocation.x);
                    if (associationsInverse.containsKey(allocation)) {
                        newRelevantRefsFirst.addAll(associationsInverse.get(allocation));
                    }
                }
                if (relevantRefsSecond.contains(allocation.x)) {
                    newRelevantRefsSecond.add((LLVMHeuristicVariable)allocation.y);
                    if (associationsInverse.containsKey(allocation)) {
                        newRelevantRefsSecond.addAll(associationsInverse.get(allocation));
                    }
                } else if (relevantRefsSecond.contains(allocation.y)) {
                    newRelevantRefsSecond.add((LLVMHeuristicVariable)allocation.x);
                    if (associationsInverse.containsKey(allocation)) {
                        newRelevantRefsSecond.addAll(associationsInverse.get(allocation));
                    }
                }
            }
            Set<LLVMHeuristicVariable> associatedFirst =
                new LinkedHashSet<LLVMHeuristicVariable>(associations.keySet());
            Set<LLVMHeuristicVariable> associatedSecond =
                new LinkedHashSet<LLVMHeuristicVariable>(associations.keySet());
            associatedFirst.retainAll(relevantRefsFirst);
            associatedSecond.retainAll(relevantRefsSecond);
            for (LLVMHeuristicVariable ref : associatedFirst) {
                LLVMAllocation allocation = allocations.get(associations.get(ref));
                newRelevantRefsFirst.add((LLVMHeuristicVariable)allocation.x);
                newRelevantRefsFirst.add((LLVMHeuristicVariable)allocation.y);
            }
            for (LLVMHeuristicVariable ref : associatedSecond) {
                LLVMAllocation allocation = allocations.get(associations.get(ref));
                newRelevantRefsSecond.add((LLVMHeuristicVariable)allocation.x);
                newRelevantRefsSecond.add((LLVMHeuristicVariable)allocation.y);
            }
            for (LLVMHeuristicRelation rel : usefulRels) {
                Set<LLVMHeuristicVariable> inRel = rel.getVariables(false);
                if (!Collections.disjoint(inRel, relevantRefsFirst)) {
                    newRelevantRefsFirst.addAll(inRel);
                }
                if (!Collections.disjoint(inRel, relevantRefsSecond)) {
                    newRelevantRefsSecond.addAll(inRel);
                }
            }
            newRelevantRefsFirst.removeAll(relevantRefsFirst);
            newRelevantRefsSecond.removeAll(relevantRefsSecond);
        }
        if (Collections.disjoint(relevantRefsFirst, relevantRefsSecond) &&
            !(firstExpr instanceof LLVMHeuristicConstRef) && !(secondExpr instanceof LLVMHeuristicConstRef)) {
            // we have no connection between the references of the expressions and cannot infer anything;
            // if one of the expressions is a constant, we might infer a tighter bound, so we do not need a connecting
            // reference
            return null;
        } else if (firstExpr instanceof LLVMHeuristicConstRef) {
            relevantRefsFirst = relevantRefsSecond;
        }
        // relevantRefsFirst and relevantRefsSecond contain the same references - just take one
        // keep only those relations which have at least two relevant references
        Iterator<LLVMHeuristicRelation> itr = usefulRels.iterator();
        while (itr.hasNext()) {
            LLVMHeuristicRelation rel = itr.next();
            boolean foundOne = false;
            boolean remove = true;
            for (LLVMHeuristicVariable ref : rel.getVariables(false)) {
                if (relevantRefsFirst.contains(ref)) {
                    if (foundOne) {
                        remove = false;
                        break;
                    } else {
                        foundOne = true;
                    }
                }
            }
            if (remove) {
                itr.remove();
            }
        }
        return usefulRels;
    }

    /**
     * @param op Some operation.
     * @return True if the specified operation contains anything but addition/subtraction of references.
     *         False otherwise.
     */
    private static boolean containsArrayPatternViolation(LLVMHeuristicOperation op) {
        LLVMHeuristicTerm lhs = op.getLhs();
        LLVMHeuristicTerm rhs = op.getRhs();
        switch (op.getOperation()) {
            case ADD:
            case SUB:
                if (lhs instanceof LLVMHeuristicOperation) {
                    if (rhs instanceof LLVMHeuristicOperation) {
                        return
                            LLVMHeuristicIntegerState.containsArrayPatternViolation((LLVMHeuristicOperation)lhs)
                            || LLVMHeuristicIntegerState.containsArrayPatternViolation((LLVMHeuristicOperation)rhs);
                    }
                    return LLVMHeuristicIntegerState.containsArrayPatternViolation((LLVMHeuristicOperation)lhs);
                } else if (rhs instanceof LLVMHeuristicOperation) {
                    return LLVMHeuristicIntegerState.containsArrayPatternViolation((LLVMHeuristicOperation)rhs);
                }
                return false;
            case MUL:
                if (lhs instanceof LLVMHeuristicConstRef) {
                    if (((LLVMHeuristicConstRef)lhs).getIntegerValue().abs().compareTo(BigInteger.ONE) == 0) {
                        if (rhs instanceof LLVMHeuristicOperation) {
                            return LLVMHeuristicIntegerState.containsArrayPatternViolation((LLVMHeuristicOperation)rhs);
                        }
                        return false;
                    }
                } else if (rhs instanceof LLVMHeuristicConstRef) {
                    if (((LLVMHeuristicConstRef)rhs).getIntegerValue().abs().compareTo(BigInteger.ONE) == 0) {
                        if (lhs instanceof LLVMHeuristicOperation) {
                            return LLVMHeuristicIntegerState.containsArrayPatternViolation((LLVMHeuristicOperation)lhs);
                        }
                        return false;
                    }
                }
                // fall through
            default:
                return true;
        }
    }

    /**
     * Adds to the specified toExprs set of expressions those expressions emerging from the ones contained in the
     * fromExprs set by replacing some references by extreme constants such that the original expression is known to be
     * in the desired relation to the added expression by the specified value function.
     * @param values Value function.
     * @param fromExprs A set of expressions.
     * @param toExprs Another set of expressions.
     * @param strict Strict or weak relation?
     * @param greater Greater or less than?
     */
    private static void handleValues(
        ImmutableMap<LLVMHeuristicVariable, LLVMValue> values,
        Set<LLVMHeuristicTerm> fromExprs,
        Set<LLVMHeuristicTerm> toExprs,
        boolean strict,
        boolean greater
    ) {
        // be safe - fromExprs and toExprs might be the very same set
        Set<LLVMHeuristicTerm> newExprs = new LinkedHashSet<LLVMHeuristicTerm>();
        for (LLVMHeuristicTerm expr : fromExprs) {
            newExprs.addAll(LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(expr, values, strict, greater));
        }
        toExprs.addAll(newExprs);
    }

    /**
     * @param relType The relation type.
     * @return YES if the relation holds for equal expressions, NO otherwise.
     */
    private static YNM truthValueForEqualExpressions(IntegerRelationType relType) {
        switch (relType) {
            case EQ:
            case LE:
            case GE:
                return YNM.YES;
            case NE:
            case GT:
            case LT:
                return YNM.NO;
            default:
                throw new IllegalStateException("Someone found a new way to relate integers...");
        }
    }

    /**
     * @param knownRelations The known relations.
     * @param ref The reference to be checked.
     * @param c The (constant) alignment to check.
     * @param useCache Should we use the cache?
     * @return YES if the given alignment holds, NO if it does not hold, and MAYBE otherwise.
     */
    private static YNM truthValueOfAlignment(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicVariable ref,
        LLVMHeuristicConstRef c,
        boolean useCache
    ) {
            if (c.getIntegerValue().compareTo(BigInteger.ZERO) <= 0) {
                return YNM.MAYBE;
            }
            if (ref instanceof LLVMHeuristicConstRef) {
                BigInteger x = ((LLVMHeuristicConstRef) ref).getIntegerValue();
                if (x.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                    return YNM.YES;
                } else {
                    return YNM.NO;
                }
            } else {
                if (
                    LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                        knownRelations,
                        ref,
                        c,
                        new HashSet<LLVMHeuristicVariable>(),
                        useCache
                    ).equals(YNM.YES))
                {
                    return YNM.YES;
                }
            }
        return YNM.MAYBE;
    }

    private static YNM truthValueOfAlignmentByPropagation(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicVariable ref,
        LLVMHeuristicConstRef c,
        HashSet<LLVMHeuristicVariable> visited,
        boolean useCache
    ) {
        // First check if there exists such a relation.
        if (
            LLVMHeuristicIntegerState.truthValueOfAlignmentByRelationCheck(
                knownRelations,
                ref,
                c,
                useCache
            ).equals(YNM.YES))
        {
            return YNM.YES;
        }
        // Check if we can propagate information, which is the case if
        // - we want to check 'ref mod c = 0'
        // - we have a relation 'ref = y + z*c'
        // - we have a relation 'y mod c = 0'
        visited.add(ref);
        for (LLVMHeuristicRelation rel : knownRelations) {
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            if (lhs.equals(ref)
                && rhs instanceof LLVMHeuristicOperation
                && ((LLVMHeuristicOperation)rhs).getOperation() == ArithmeticOperationType.ADD)
            {
                LLVMHeuristicOperation op = (LLVMHeuristicOperation)rhs;
                if (!(op.getLhs() instanceof LLVMHeuristicConstRef)
                    && !(visited.contains(op.getLhs())))
                {
                    boolean addendDivByC = false;
                    if (op.getRhs() instanceof LLVMHeuristicConstRef) {
                        // we have a relation 'ref = y + c2'
                        // check if c2 = z*c
                        BigInteger c2 = ((LLVMHeuristicConstRef)op.getRhs()).getIntegerValue();
                        if (c2.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                            addendDivByC = true;
                        }
                    } else if (op.getRhs() instanceof LLVMHeuristicOperation
                        && ((LLVMHeuristicOperation)op.getRhs()).getOperation() == ArithmeticOperationType.MUL)
                    {
                        // we have a relation 'ref = y + z1*z2'
                        // check if z1 or z2 is constant and divisible by c
                        LLVMHeuristicOperation addend = (LLVMHeuristicOperation)op.getRhs();
                        if (addend.getLhs() instanceof LLVMHeuristicConstRef) {
                            BigInteger c3 = ((LLVMHeuristicConstRef)addend.getLhs()).getIntegerValue();
                            if (c3.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                                addendDivByC = true;
                            }
                        } else if (addend.getRhs() instanceof LLVMHeuristicConstRef) {
                            BigInteger c3 = ((LLVMHeuristicConstRef)addend.getRhs()).getIntegerValue();
                            if (c3.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                                addendDivByC = true;
                            }
                        }
                    }
                    if (addendDivByC) {
                        if (
                            LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                                knownRelations,
                                (LLVMHeuristicVariable)op.getLhs(),
                                c,
                                visited,
                                useCache
                            ).equals(YNM.YES))
                        {
                            return YNM.YES;
                        }
                    }
                }
                if (!(op.getRhs() instanceof LLVMHeuristicConstRef)
                    && !(visited.contains(op.getRhs())))
                {
                    boolean addendDivByC = false;
                    if (op.getLhs() instanceof LLVMHeuristicConstRef) {
                        // we have a relation 'ref = c2 + y'
                        // check if c2 = z*c
                        BigInteger c2 = ((LLVMHeuristicConstRef)op.getLhs()).getIntegerValue();
                        if (c2.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                            addendDivByC = true;
                        }
                    } else if (op.getLhs() instanceof LLVMHeuristicOperation
                        && ((LLVMHeuristicOperation)op.getLhs()).getOperation() == ArithmeticOperationType.MUL)
                    {
                        // we have a relation 'ref = z1*z2 + y'
                        // check if z1 or z2 is constant and divisible by c
                        LLVMHeuristicOperation addend = (LLVMHeuristicOperation)op.getLhs();
                        if (addend.getLhs() instanceof LLVMHeuristicConstRef) {
                            BigInteger c3 = ((LLVMHeuristicConstRef)addend.getLhs()).getIntegerValue();
                            if (c3.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                                addendDivByC = true;
                            }
                        } else if (addend.getRhs() instanceof LLVMHeuristicConstRef) {
                            BigInteger c3 = ((LLVMHeuristicConstRef)addend.getRhs()).getIntegerValue();
                            if (c3.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                                addendDivByC = true;
                            }
                        }
                    }
                    if (addendDivByC) {
                        if (
                            LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                                knownRelations,
                                (LLVMHeuristicVariable)op.getRhs(),
                                c,
                                visited,
                                useCache
                            ).equals(YNM.YES))
                        {
                            return YNM.YES;
                        }
                    }
                }
            } else if (rhs.equals(ref)
                && lhs instanceof LLVMHeuristicOperation
                && ((LLVMHeuristicOperation)lhs).getOperation() == ArithmeticOperationType.ADD)
            {
                LLVMHeuristicOperation op = (LLVMHeuristicOperation)lhs;
                if (!(op.getLhs() instanceof LLVMHeuristicConstRef)
                    && !(visited.contains(op.getLhs())))
                {
                    boolean addendDivByC = false;
                    if (op.getRhs() instanceof LLVMHeuristicConstRef) {
                        // we have a relation 'y + c2 = ref'
                        // check if c2 = z*c
                        BigInteger c2 = ((LLVMHeuristicConstRef)op.getRhs()).getIntegerValue();
                        if (c2.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                            addendDivByC = true;
                        }
                    } else if (op.getRhs() instanceof LLVMHeuristicOperation
                        && ((LLVMHeuristicOperation)op.getRhs()).getOperation() == ArithmeticOperationType.MUL)
                    {
                        // we have a relation 'y + z1*z2 = ref'
                        // check if z1 or z2 is constant and divisible by c
                        LLVMHeuristicOperation addend = (LLVMHeuristicOperation)op.getRhs();
                        if (addend.getLhs() instanceof LLVMHeuristicConstRef) {
                            BigInteger c3 = ((LLVMHeuristicConstRef)addend.getLhs()).getIntegerValue();
                            if (c3.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                                addendDivByC = true;
                            }
                        } else if (addend.getRhs() instanceof LLVMHeuristicConstRef) {
                            BigInteger c3 = ((LLVMHeuristicConstRef)addend.getRhs()).getIntegerValue();
                            if (c3.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                                addendDivByC = true;
                            }
                        }
                    }
                    if (addendDivByC) {
                        if (
                            LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                                knownRelations,
                                (LLVMHeuristicVariable)op.getLhs(),
                                c,
                                visited,
                                useCache
                            ).equals(YNM.YES))
                        {
                            return YNM.YES;
                        }
                    }
                }
                if (!(op.getRhs() instanceof LLVMHeuristicConstRef)
                    && !(visited.contains(op.getRhs())))
                {
                    boolean addendDivByC = false;
                    if (op.getLhs() instanceof LLVMHeuristicConstRef) {
                        // we have a relation 'c2 + y = ref'
                        // check if c2 = z*c
                        BigInteger c2 = ((LLVMHeuristicConstRef)op.getLhs()).getIntegerValue();
                        if (c2.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                            addendDivByC = true;
                        }
                    } else if (op.getLhs() instanceof LLVMHeuristicOperation
                        && ((LLVMHeuristicOperation)op.getLhs()).getOperation() == ArithmeticOperationType.MUL)
                    {
                        // we have a relation 'z1*z2 + y = ref'
                        // check if z1 or z2 is constant and divisible by c
                        LLVMHeuristicOperation addend = (LLVMHeuristicOperation)op.getLhs();
                        if (addend.getLhs() instanceof LLVMHeuristicConstRef) {
                            BigInteger c3 = ((LLVMHeuristicConstRef)addend.getLhs()).getIntegerValue();
                            if (c3.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                                addendDivByC = true;
                            }
                        } else if (addend.getRhs() instanceof LLVMHeuristicConstRef) {
                            BigInteger c3 = ((LLVMHeuristicConstRef)addend.getRhs()).getIntegerValue();
                            if (c3.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                                addendDivByC = true;
                            }
                        }
                    }
                    if (addendDivByC) {
                        if (
                            LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                                knownRelations,
                                (LLVMHeuristicVariable)op.getRhs(),
                                c,
                                visited,
                                useCache
                            ).equals(YNM.YES))
                        {
                            return YNM.YES;
                        }
                    }
                }
            // now check if we have something like 'y = ref + z*c'
            } else if (lhs instanceof LLVMHeuristicVariable
                && !(visited.contains(lhs))
                && rhs instanceof LLVMHeuristicOperation
                && ((LLVMHeuristicOperation)rhs).getOperation() == ArithmeticOperationType.ADD)
            {
                LLVMHeuristicVariable y = (LLVMHeuristicVariable)lhs;
                LLVMHeuristicOperation op = (LLVMHeuristicOperation)rhs;
                if (op.getLhs().equals(ref)
                    && op.getRhs() instanceof LLVMHeuristicConstRef)
                {
                    // we have a relation 'y = ref + c2'
                    // check if c2 = z*c
                    BigInteger c2 = ((LLVMHeuristicConstRef)op.getRhs()).getIntegerValue();
                    if (c2.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                        if (
                            LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                                knownRelations,
                                y,
                                c,
                                visited,
                                useCache
                            ).equals(YNM.YES))
                        {
                            return YNM.YES;
                        }
                    }
                }
                if (op.getLhs() instanceof LLVMHeuristicConstRef
                    && op.getRhs().equals(ref))
                {
                    // we have a relation 'y = c2 + ref'
                    // check if c2 = z*c
                    BigInteger c2 = ((LLVMHeuristicConstRef)op.getLhs()).getIntegerValue();
                    if (c2.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                        if (
                            LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                                knownRelations,
                                y,
                                c,
                                visited,
                                useCache
                            ).equals(YNM.YES))
                        {
                            return YNM.YES;
                        }
                    }
                }
            // now check if we have something like 'ref + z*c = y'
            } else if (rhs instanceof LLVMHeuristicVariable
                && !(visited.contains(rhs))
                && lhs instanceof LLVMHeuristicOperation
                && ((LLVMHeuristicOperation)lhs).getOperation() == ArithmeticOperationType.ADD)
            {
                LLVMHeuristicVariable y = (LLVMHeuristicVariable)rhs;
                LLVMHeuristicOperation op = (LLVMHeuristicOperation)lhs;
                if (op.getLhs().equals(ref)
                    && op.getRhs() instanceof LLVMHeuristicConstRef)
                {
                    // we have a relation 'ref + c2 = y'
                    // check if c2 = z*c
                    BigInteger c2 = ((LLVMHeuristicConstRef)op.getRhs()).getIntegerValue();
                    if (c2.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                        if (
                            LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                                knownRelations,
                                y,
                                c,
                                visited,
                                useCache
                            ).equals(YNM.YES))
                        {
                            return YNM.YES;
                        }
                    }
                }
                if (op.getLhs() instanceof LLVMHeuristicConstRef
                    && op.getRhs().equals(ref))
                {
                    // we have a relation 'c2 + ref = y'
                    // check if c2 = z*c
                    BigInteger c2 = ((LLVMHeuristicConstRef)op.getLhs()).getIntegerValue();
                    if (c2.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                        if (
                            LLVMHeuristicIntegerState.truthValueOfAlignmentByPropagation(
                                knownRelations,
                                y,
                                c,
                                visited,
                                useCache
                            ).equals(YNM.YES))
                        {
                            return YNM.YES;
                        }
                    }
                }
            }
        }
        return YNM.MAYBE;
    }

    /**
     * @param knownRelations The known relations.
     * @param ref The reference to be checked.
     * @param c The (constant) alignment to check.
     * @param useCache Should we use the cache?
     * @return YES if the given alignment holds, NO if it does not hold, and MAYBE otherwise.
     */
    private static YNM truthValueOfAlignmentByRelationCheck(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicVariable ref,
        LLVMHeuristicConstRef c,
        boolean useCache
    ) {
        for (LLVMHeuristicRelation rel : knownRelations) {
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            if (lhs instanceof LLVMHeuristicConstRef
                && ((LLVMHeuristicConstRef)lhs).getIntegerValue().equals(BigInteger.ZERO)
                && rhs instanceof LLVMHeuristicOperation
                && ((LLVMHeuristicOperation)rhs).getOperation() == ArithmeticOperationType.EMOD
                && ((LLVMHeuristicOperation)rhs).getRhs() instanceof LLVMHeuristicConstRef
                && ((LLVMHeuristicOperation)rhs).getLhs().equals(ref))
            {
                BigInteger knownAlignment =
                    ((LLVMHeuristicConstRef)((LLVMHeuristicOperation)rhs).getRhs()).getIntegerValue();
                if (knownAlignment.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                    return YNM.YES;
                }
            }
            if (rhs instanceof LLVMHeuristicConstRef
                && ((LLVMHeuristicConstRef) rhs).getIntegerValue().equals(BigInteger.ZERO)
                && lhs instanceof LLVMHeuristicOperation
                && ((LLVMHeuristicOperation)lhs).getOperation() == ArithmeticOperationType.EMOD
                && ((LLVMHeuristicOperation)lhs).getRhs() instanceof LLVMHeuristicConstRef
                && ((LLVMHeuristicOperation)lhs).getLhs().equals(ref))
            {
                BigInteger knownAlignment =
                    ((LLVMHeuristicConstRef)((LLVMHeuristicOperation)lhs).getRhs()).getIntegerValue();
                if (knownAlignment.mod(c.getIntegerValue()).equals(BigInteger.ZERO)) {
                    return YNM.YES;
                }
            }
        }
        return YNM.MAYBE;
    }

    /**
     * @param knownRelations The known relations.
     * @param firstExpr The first expression.
     * @param secondExpr The second expression.
     * @param useCache Should we use the cache?
     * @return YES if we have an alignment relation which holds, NO we have an alignment relation which does not hold,
     *         and MAYBE otherwise.
     */
    private static YNM truthValueOfAlignmentRelation(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicTerm secondExpr,
        boolean useCache
    ) {
        LLVMHeuristicConstRef zero;
        LLVMHeuristicOperation op;
        if (firstExpr instanceof LLVMHeuristicConstRef && secondExpr instanceof LLVMHeuristicOperation) {
            zero = (LLVMHeuristicConstRef)firstExpr;
            op = (LLVMHeuristicOperation)secondExpr;
        } else if (secondExpr instanceof LLVMHeuristicConstRef && firstExpr instanceof LLVMHeuristicOperation) {
            zero = (LLVMHeuristicConstRef)secondExpr;
            op = (LLVMHeuristicOperation)firstExpr;

        } else {
            return YNM.MAYBE;
        }
        if (
            op.isSimple()
            && op.getOperation() == ArithmeticOperationType.EMOD
            && zero.getIntegerValue().equals(BigInteger.ZERO)
            && op.getRhs() instanceof LLVMHeuristicConstRef
        ) {
            // we have a relation '0 = ref mod c' or 'ref mod c = 0'
            return
                LLVMHeuristicIntegerState.truthValueOfAlignment(
                    knownRelations,
                    (LLVMHeuristicVariable)op.getLhs(),
                    (LLVMHeuristicConstRef)op.getRhs(),
                    useCache
                );
        }
        return YNM.MAYBE;
    }

    /**
     * Only keep those expressions in old and new knowledge which are not improved by the other one, whose number of
     * variable occurrences does not exceed the maximal number of such occurrences within the useful relations, and
     * where there is no constant multiplicative factor whose absolute value is bigger than that of any such factor
     * occurring in the useful relations. Moreover, if the useful relations adhere to an array index pattern (base
     * address + factor times index), drop expressions not matching this pattern.
     * @param maxNumOfVarOccs The maximal number of variable occurrences within an expression we are looking for.
     * @param highestFactor The maximal absolute multiplicative constant factor occurring in an expression we are
     *                      looking for.
     * @param arrayPatterns A set of array patterns (base address and factor) if the useful relations adhere to array
     *                      patterns. Null otherwise.
     * @param oldSet The old knowledge.
     * @param newSet The new knowledge.
     * @param weakStrictMix True if old knowledge is strict and new knowledge is weak (don't delete old knowledge then).
     * @param strict Are we looking for a strict relation?
     * @param greater Is the direction greater or less than?
     * @param goal The expression we want to reach in linearized form.
     * @param inDirection Is the new set in the desired or opposite direction?
     * @param strictToGoal Do we need a strict or weak relation from the new set to the goal?
     * @return YES, if we already reached the goal expression and look into the right direction, NO if the former
     *         holds, but the latter not, and MAYBE otherwise.
     */
    private static YNM updateWithOldKnowledge(
        int maxNumOfVarOccs,
        BigInteger highestFactor,
        Set<Pair<LLVMHeuristicVariable, BigInteger>> arrayPatterns,
        Set<LLVMHeuristicTerm> oldSet,
        Set<LLVMHeuristicTerm> newSet,
        boolean weakStrictMix,
        boolean strict,
        boolean greater,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> goal,
        boolean inDirection,
        boolean strictToGoal
    ) {
        Set<LLVMHeuristicTerm> oldToDel = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> newToDel = new LinkedHashSet<LLVMHeuristicTerm>();
        for (LLVMHeuristicTerm oldExpr : oldSet) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> oldLinear = oldExpr.toLinear();
            if (
                oldLinear.x == null
                || oldLinear.x.getNumberOfVarOccs() > maxNumOfVarOccs
                || oldExpr.computeHighestAbsoluteFactor().compareTo(highestFactor) > 0
                || !LLVMHeuristicIntegerState.adheresToArrayPatterns(oldExpr, arrayPatterns)
            ) {
                oldToDel.add(oldExpr);
                continue;
            }
            for (LLVMHeuristicTerm newExpr : newSet) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> newLinear = newExpr.toLinear();
                if (oldLinear.x.equals(newLinear.x) && oldLinear.z.compareTo(newLinear.z) == 0) {
                    if (LLVMHeuristicIntegerState.isInRelation(oldLinear.y, newLinear.y, false, greater)) {
                        newToDel.add(newExpr);
                    } else if (!weakStrictMix) {
                        oldToDel.add(oldExpr);
                    }
                }
            }
            newSet.removeAll(newToDel);
            newToDel.clear();
        }
        Set<LLVMHeuristicTerm> remNew = new LinkedHashSet<LLVMHeuristicTerm>(newSet);
        for (LLVMHeuristicTerm newExpr : newSet) {
            remNew.remove(newExpr);
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> newLinear = newExpr.toLinear();
            if (
                newLinear.x == null
                || newLinear.x.getNumberOfVarOccs() > maxNumOfVarOccs
                || newExpr.computeHighestAbsoluteFactor().compareTo(highestFactor) > 0
                || !LLVMHeuristicIntegerState.adheresToArrayPatterns(newExpr, arrayPatterns)
            ) {
                newToDel.add(newExpr);
            } else {
                if (
                    newLinear.x.equals(goal.x)
                    && newLinear.z.compareTo(goal.z) == 0
                    && LLVMHeuristicIntegerState.isInRelation(newLinear.y, goal.y, strictToGoal, greater)
                ) {
                    return inDirection ? YNM.YES : YNM.NO;
                }
                for (LLVMHeuristicTerm other : remNew) {
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherLinear = other.toLinear();
                    if (
                        otherLinear.x != null
                        && otherLinear.x.equals(newLinear.x)
                        && otherLinear.z.compareTo(newLinear.z) == 0
                    ) {
                        if (LLVMHeuristicIntegerState.isInRelation(otherLinear.y, newLinear.y, false, greater)) {
                            newToDel.add(newExpr);
                        } else {
                            newToDel.add(other);
                        }
                    }
                }
            }
        }
        newSet.removeAll(newToDel);
        oldSet.removeAll(oldToDel);
        return YNM.MAYBE;
    }

    /**
     * Have the values been adjusted?
     */
    private final boolean adjusted;

    /**
     * Mapping from references to the maximal additional number of memory cells occupied by a referenced value such
     * that this reference is still associated. Should be the same as in the corresponding LLVMHeuristicState.
     */
    private final ImmutableMap<LLVMHeuristicVariable, BigInteger> associationOffsets;

    /**
     * Mapping from references to the index of the corresponding allocated memory area. Should be the same as in the
     * corresponding LLVMHeuristicState.
     */
    private final ImmutableMap<LLVMHeuristicVariable, Integer> associations;

    /**
     * The call stack. Should be the same as in the corresponding LLVMHeuristicState.
     */
    private final ImmutableDeque<LLVMReturnInformation> callStack;

    /**
     * Are the relations clean?
     */
    private final boolean clean;

    /**
     * Stores references different from parameters and allocation borders which are given by the initial knowledge.
     * These are always considered as used. Should be the same as in the corresponding LLVMHeuristicState.
     */
    private final ImmutableMap<Integer, LLVMHeuristicVariable> initialHeapAddresses;

    /**
     * Strategy parameters.
     */
    private final LLVMParameters params;

    /**
     * Contains all important relations for this state.
     */
    private final ImmutableSet<LLVMHeuristicRelation> relations;

    /**
     * Cache for unequal references. Reduces the number of SMT calls when resolving reference equalities.
     */
    private final ImmutableSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> unequalCache;

    /**
     * Contains all integer values of this state. Note: All values are represented internally as signed integers that
     * describe all possible bit patterns. If you want to read a value using a different interpretation of the bit
     * pattern, you will need to convert.
     */
    private final ImmutableMap<LLVMHeuristicVariable, LLVMValue> values;

    /**
     * Contains all variables of this state. Should be the same as in the corresponding LLVMHeuristicState.
     */
    private final ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> variables;

    /**
     * @param rels The relations.
     * @param vals The values.
     * @param unequals The unequal-cache.
     * @param newVariables The variable function.
     * @param newHeap The heap function.
     * @param newAllocatedMemory The memory areas.
     * @param newAssociations The associations (reference to memory area).
     * @param newAssociationOffsets The association offsets (additional memory cells occupied within association).
     * @param newCallStack The call stack.
     * @param initialHeapAddrs The initial heap addresses.
     * @param cleanParam Are the relations clean?
     * @param adjustedParam Have the values been adjusted?
     * @param parameters Strategy parameters.
     */
    public LLVMHeuristicIntegerState(
        ImmutableSet<LLVMHeuristicRelation> rels,
        ImmutableMap<LLVMHeuristicVariable, LLVMValue> vals,
        ImmutableSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> unequals,
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVariables,
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> newHeap,
        ImmutableList<LLVMAllocation> newAllocatedMemory,
        ImmutableMap<LLVMHeuristicVariable, Integer> newAssociations,
        ImmutableMap<LLVMHeuristicVariable, BigInteger> newAssociationOffsets,
        ImmutableDeque<LLVMReturnInformation> newCallStack,
        ImmutableMap<Integer, LLVMHeuristicVariable> initialHeapAddrs,
        boolean cleanParam,
        boolean adjustedParam,
        LLVMParameters parameters
    ) {
        super(null, newAllocatedMemory, newHeap, null);
        this.relations = rels;
        this.values = vals;
        this.unequalCache = unequals;
        this.variables = newVariables;
        this.associations = newAssociations;
        this.associationOffsets = newAssociationOffsets;
        this.callStack = newCallStack;
        this.initialHeapAddresses = initialHeapAddrs;
        this.clean = cleanParam;
        this.adjusted = adjustedParam;
        this.params = parameters;
    }

    /**
     * Creates an empty heuristic integer state.
     * @param parameters Strategy parameters.
     */
    public LLVMHeuristicIntegerState(LLVMParameters parameters) {
        this(
            ImmutableCreator.create(Collections.emptySet()),
            ImmutableCreator.create(Collections.emptyMap()),
            ImmutableCreator.create(Collections.emptySet()),
            ImmutableCreator.create(Collections.emptyMap()),
            ImmutableCreator.create(Collections.emptyMap()),
            ImmutableCreator.create(Collections.emptyList()),
            ImmutableCreator.create(Collections.emptyMap()),
            ImmutableCreator.create(Collections.emptyMap()),
            ImmutableCreator.create(new ArrayDeque<LLVMReturnInformation>()),
            ImmutableCreator.create(Collections.emptyMap()),
            true,
            true,
            parameters
        );
    }

    /**
     * @param ref1 A non-constant reference.
     * @param ref2 Another non-constant reference.
     * @param aborter For abortions.
     * @return A state emerging from this state by adding and caching the knowledge that the specified references are
     *         unequal.
     */
    public LLVMHeuristicIntegerState addReferenceInequalities(
        LLVMHeuristicVarRef ref1,
        LLVMHeuristicVarRef ref2,
        Abortion aborter
    ) {
        if (Globals.useAssertions) {
            assert (ref1 != null && ref2 != null) : "References must not be null!";
            assert (!ref1.equals(ref2)) : "Equal references cannot be unequal!";
        }
        ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef> pair =
            new ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>(ref1, ref2);
        if (this.getUnequalCache().contains(pair)) {
            return this;
        }
        Set<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> newUnequalCache =
            new LinkedHashSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>>(this.getUnequalCache());
        newUnequalCache.add(pair);
        newUnequalCache.add(new ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>(ref2, ref1));
        LLVMHeuristicRelationSet set = new LLVMHeuristicRelationSet(this.getRelations());
        set.addRelation(this, this.getRelationFactory().notEqualTo(ref1, ref2), true, aborter);
        return
            new LLVMHeuristicIntegerState(
                ImmutableCreator.create(set),
                this.getValues(),
                ImmutableCreator.create(newUnequalCache),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    @Override
    public LLVMHeuristicIntegerState addRelation(IntegerRelation relation, Abortion aborter) {
        return
            this.addRelation(
                LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY.createRelation(relation),
                aborter
            );
    }

    /**
     * @param relation Some relation.
     * @param aborter For abortions.
     * @return An integer state emerging from adding as much of the knowledge encoded by the specified relation as
     *         possible.
     */
    public LLVMHeuristicIntegerState addRelation(LLVMHeuristicRelation relation, Abortion aborter) {
        if (relation.isSimple() && relation.isUndirectedInequality()) {
            LLVMHeuristicVariable left = (LLVMHeuristicVariable)relation.getLhs();
            LLVMHeuristicVariable right = (LLVMHeuristicVariable)relation.getRhs();
            if (left instanceof LLVMHeuristicVarRef && right instanceof LLVMHeuristicVarRef) {
                return this.addReferenceInequalities((LLVMHeuristicVarRef)left, (LLVMHeuristicVarRef)right, aborter);
            }
        }
        LLVMHeuristicRelationSet set = new LLVMHeuristicRelationSet(this.getRelations());
        set.addRelation(this, relation, true, aborter);
        return
            new LLVMHeuristicIntegerState(
                ImmutableCreator.create(set),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    @Override
    public LLVMHeuristicIntegerState addRelationSet(Iterable<? extends IntegerRelation> rels, Abortion aborter) {
        LLVMHeuristicRelationSet set = new LLVMHeuristicRelationSet(this.relations);
        Set<LLVMHeuristicRelation> newRels = new LinkedHashSet<LLVMHeuristicRelation>();
        for (IntegerRelation rel : rels) {
            newRels.add(LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY.createRelation(rel));
        }
        set.addRelations(this, newRels, true, aborter);
        return
            new LLVMHeuristicIntegerState(
                ImmutableCreator.create(set),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    @Override
    public LLVMHeuristicIntegerState associateAccess(
        LLVMSymbolicVariable pointerParam,
        LLVMPointerType type,
        Integer index,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        LLVMHeuristicVariable pointer = (LLVMHeuristicVariable)pointerParam;
        LLVMHeuristicIntegerState res = this;
        BigInteger offset = type.toOffset();
        if (
            (this.getAssociations().containsKey(pointer) && !this.getAssociations().get(pointer).equals(index))
            || !this.getAssociationOffsets().containsKey(pointer)
            || this.getAssociationOffsets().get(pointer).compareTo(offset) < 0
        ) {
            Map<LLVMHeuristicVariable, Integer> newAssocFunc =
                new LinkedHashMap<LLVMHeuristicVariable, Integer>(this.getAssociations());
            
            Map<LLVMHeuristicVariable, BigInteger> newAssocOffset =
                new LinkedHashMap<LLVMHeuristicVariable, BigInteger>(this.getAssociationOffsets());
            
            newAssocOffset.put(pointer, offset);
            newAssocFunc.put(pointer, index);
            res = res.setAssociations(newAssocFunc).setAssociationOffsets(newAssocOffset);
        }
        return
            res.initializeValue(
                pointer,
                type.getInitializedIntValue(true, this.params.useBoundedIntegers).removeZeroFromInteger()
            );
    }

    /**
     * @param associations Non-null, contains pairs of references to the first and last element of memory blocks
     *                     created by alloc.
     * @param associationOffsets The association offsets.
     * @param allocatedMemory List of allocated memory blocks.
     * @return An SMT expression that encodes where certain pointers can be found (x \in [x,y] or x \in [y,x] is
     *         omitted, we know that from the allocations already).
     */
    public SMTExpression<SBool> associationInformationToSMTExp() {
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        List<SMTExpression<SBool>> subformulas = new ArrayList<SMTExpression<SBool>>();
        // Look at all those associations.
        for (Map.Entry<LLVMHeuristicVariable, Integer> refToAllocIndex : this.getAssociations().entrySet()) {
            LLVMHeuristicVariable ref = refToAllocIndex.getKey();
            int index = refToAllocIndex.getValue();
            LLVMAllocation allocBlock = this.getAllocations().get(index);
            // If the reference is a first or last element of its allocation block,
            // then we need not represent anything (except we have an association offset).
            LLVMHeuristicVariable lower = (LLVMHeuristicVariable)allocBlock.x;
            BigInteger offset = this.getAssociationOffsets().get(ref);
            if (lower.equals(ref) && offset.compareTo(BigInteger.ZERO) == 0) {
                continue;
            }
            LLVMHeuristicVariable upper = (LLVMHeuristicVariable)allocBlock.y;
            if (upper.equals(ref)) {
                continue;
            }
            // Ah, so ref can truly benefit from the association information.
            subformulas.add(Ints.lessEqual(lower.toSMTExp(), ref.toSMTExp()));
            subformulas.add(Ints.lessEqual(termFactory.upperAddress(ref, offset).toSMTExp(), upper.toSMTExp()));
        }
        return Core.and(subformulas);
    }

    @Override
    public Pair<Boolean, ? extends LLVMHeuristicIntegerState> checkRelation(
        IntegerRelation relation,
        Abortion aborter
    ) {
        return
            new Pair<Boolean, LLVMHeuristicIntegerState>(
                this.truthValueOfRelation(this.getRelationFactory().createRelation(relation), true, aborter) == YNM.YES,
                this
            );
    }

    @Override
    public Pair<LLVMAssociationIndex, ? extends LLVMIntegerState> getAssociatedAllocationIndex(
        LLVMTerm term,
        LLVMPointerType type,
        boolean oneMore,
        Abortion aborter
    ) {
        if (term instanceof LLVMHeuristicVariable) {
            LLVMHeuristicVariable var = (LLVMHeuristicVariable)term;
            Integer res = this.getAssociations().get(var);
            if (res != null && this.getAssociationOffsets().get(var).compareTo(type.toOffset()) >= 0) {
                return new Pair<LLVMAssociationIndex, LLVMIntegerState>(new LLVMAssociationIndex(res, false), this);
            }
        }
        Pair<LLVMAssociationIndex, ? extends LLVMIntegerState> superRes = 
         super.getAssociatedAllocationIndex(term, type, oneMore, aborter);
        return superRes;
    }

    /**
     * @return A mapping from references to the maximal additional number of memory cells occupied by values referenced
     *         by the corresponding references such that they are still associated to an allocation.
     */
    public ImmutableMap<LLVMHeuristicVariable, BigInteger> getAssociationOffsets() {
        return this.associationOffsets;
    }

    /**
     * @return The associations. Here a reference and target type are mapped to the index of the corresponding
     *         allocation memory block in the allocation list.
     */
    public ImmutableMap<LLVMHeuristicVariable, Integer> getAssociations() {
        return this.associations;
    }

    /**
     * @return The call stack.
     */
    public ImmutableDeque<LLVMReturnInformation> getCallStack() {
        return this.callStack;
    }

    /**
     * @return The initial heap addresses.
     */
    public ImmutableMap<Integer, LLVMHeuristicVariable> getInitialHeapAddresses() {
        return this.initialHeapAddresses;
    }

    /**
     * @return A map from variable names to references.
     */
    public ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> getProgramVariables() {
        return this.variables;
    }

    /**
     * @return The relations.
     */
    public ImmutableSet<LLVMHeuristicRelation> getRelations() {
        return this.relations;
    }

    /**
     * @param rel Some relation.
     * @return The strongest version of this relation we could find, i.e., if we have x != y and the state has x <= y,
     *         we return x < y.
     * TODO: Find more interesting cases. There's always more.
     */
    public LLVMHeuristicRelationSet getStrongestRelations(LLVMHeuristicRelation rel, Abortion aborter) {
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        LLVMHeuristicRelationSet res = new LLVMHeuristicRelationSet();
        switch (rel.getHeuristicRelationType()) {
            case NE:
                if (
                    this.truthValueOfRelation(
                        rel.getLhs(),
                        LLVMHeuristicRelationType.LE,
                        rel.getRhs(),
                        true,
                        aborter
                    ) == YNM.YES
                ) {
                    res.add(relationFactory.lessThan(rel.getLhs(), rel.getRhs()));
                } else if (
                    this.truthValueOfRelation(
                        rel.getRhs(),
                        LLVMHeuristicRelationType.LE,
                        rel.getLhs(),
                        true,
                        aborter
                    ) == YNM.YES
                ) {
                    res.add(relationFactory.lessThan(rel.getRhs(), rel.getLhs()));
                } else {
                    res.add(rel);
                }
                break;
            case EQ:
                if (rel.isSimple() && rel.getLhs().equals(rel.getRhs())) {
                    LLVMHeuristicVariable eqRef = (LLVMHeuristicVariable)rel.getLhs();
                    if (!eqRef.isConcrete()) {
                        AbstractBoundedInt eqIntVal = this.getValue(eqRef).getThisAsAbstractBoundedInt();
                        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> inv: this.getMemory().entrySet()) {
                            assert (inv.getKey().isPointwise());
                            LLVMHeuristicVariable heapValRef =
                                (LLVMHeuristicVariable)((LLVMSimpleMemoryInvariant)inv.getValue()).getPointedToValue();
                            if (
                                heapValRef.isConcrete()
                                && !eqIntVal.containsLiteral(((LLVMHeuristicConstRef)heapValRef).getIntegerValue())
                            ) {
                                res.addAll(this.getStrongestRelations(relationFactory.notEqualTo(eqRef, heapValRef), aborter));
                            }
                        }
                    }
                } else {
                    res.add(rel);
                }
                break;
            default:
                res.add(rel);
        }
        return res;
    }

    /**
     * @return The cache for unequal symbolic variables.
     */
    public ImmutableSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> getUnequalCache() {
        return this.unequalCache;
    }

    /**
     * @param ref The reference to be found.
     * @return The value of the reference in the value function of this state.
     */
    public LLVMValue getValue(LLVMHeuristicVariable ref) {
        return LLVMHeuristicState.getValue(ref, this.getValues());
    }

    /**
     * @return The values.
     */
    public ImmutableMap<LLVMHeuristicVariable, LLVMValue> getValues() {
        return this.values;
    }

    /**
     * @param possiblyFresh Some symbolic variable.
     * @param initialValue The initial value for the symbolic variable.
     * @return This state where the value of the specified symbolic variable is set to the specified initial value if
     *         there has not been some value set for that variable before. Otherwise, this state is returned without
     *         modification.
     */
    public LLVMHeuristicIntegerState initializeValue(LLVMHeuristicVariable possiblyFresh, LLVMValue initialValue) {
        LLVMHeuristicIntegerState res = this;
        if (!res.getValues().containsKey(possiblyFresh)) {
            res = res.setValue(possiblyFresh, initialValue);
        }
        return res;
    }

    /**
     * @return Have the values been adjusted?
     */
    public boolean isAdjusted() {
        return this.adjusted;
    }

    /**
     * @return Are the relations clean?
     */
    public boolean isClean() {
        return this.clean;
    }

    /**
     * Replace all occurrences of one symbolic variable by another. Attention: By this method we might obtain
     * tautological relations which must be cleaned thereafter.
     * @param toReplaceVar The variable to replace.
     * @param replacementVar The variable that should be used instead.
     * @return The state where the replacement has been done.
     */
    public LLVMHeuristicIntegerState replaceSymbolicVariable(
        LLVMHeuristicVariable toReplaceVar,
        LLVMHeuristicVariable replacementVar
    ) {
        // Variables:
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVars =
            new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>(this.getProgramVariables());
        for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> e : newVars.entrySet()) {
            if (e.getValue().x.equals(toReplaceVar)) {
                e.setValue(new ImmutablePair<LLVMSymbolicVariable, LLVMType>(replacementVar, e.getValue().y));
            }
        }
        // Dereferencings:
        Map<LLVMMemoryRange, LLVMMemoryInvariant> newHeap =
            new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>(this.getMemory());
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : this.getMemory().entrySet()) {
            LLVMMemoryRange range = entry.getKey();
            LLVMMemoryRange replacedRange = range.replaceReference(toReplaceVar, replacementVar);
            if (replacedRange == null) {
                continue;
            }
            newHeap.remove(range);
            LLVMMemoryInvariant value = entry.getValue();
            if (!newHeap.containsKey(replacedRange)) {
                newHeap.put(replacedRange, value);
            } else if (Globals.useAssertions) {
                LLVMMemoryInvariant otherVal = this.getMemory().get(replacedRange);
                final boolean bothSimple =
                    otherVal instanceof LLVMSimpleMemoryInvariant && value instanceof LLVMSimpleMemoryInvariant;
                assert (
                    bothSimple
                    || (otherVal instanceof LLVMIntervalMemoryInvariant && value instanceof LLVMIntervalMemoryInvariant)
                ) : "Both invariants should have the same type!";
                if (bothSimple) {
                    assert (
                        otherVal.equals(value)
                        || (
                            ((LLVMSimpleMemoryInvariant)otherVal).getPointedToValue().equals(toReplaceVar)
                            && ((LLVMSimpleMemoryInvariant)value).getPointedToValue().equals(replacementVar)
                        ) || (
                            ((LLVMSimpleMemoryInvariant)otherVal).getPointedToValue().equals(replacementVar)
                            && ((LLVMSimpleMemoryInvariant)value).getPointedToValue().equals(toReplaceVar)
                        )
                    ) : "Replacement of reference would lead to inconsistent heap information!";
                }
            }
            // else do nothing as the replaced entry already exists (at least after the for loop below)
        }
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : newHeap.entrySet()) {
            LLVMMemoryInvariant replaced_invariant = entry.getValue().replaceReference(toReplaceVar, replacementVar);
            if (replaced_invariant != null) {
                entry.setValue(replaced_invariant);
            }
        }
        // Relations
        LLVMHeuristicRelationSet newRels = new LLVMHeuristicRelationSet(this.getRelations());
        newRels.replaceSymbolicVariable(toReplaceVar, replacementVar);
        // Values:
        Map<LLVMHeuristicVariable, LLVMValue> newVals =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMValue>(this.getValues());
        newVals.remove(toReplaceVar);
        // allocated memory
        List<LLVMAllocation> newAllocMem = new ArrayList<LLVMAllocation>(this.getAllocations());
        for (int i = 0; i < newAllocMem.size(); i++) {
            LLVMAllocation pair = newAllocMem.get(i);
            if (pair.x.equals(toReplaceVar)) {
                if (pair.y.equals(toReplaceVar)) {
                    newAllocMem.set(i, new LLVMAllocation(replacementVar, replacementVar));
                } else {
                    newAllocMem.set(i, new LLVMAllocation(replacementVar, pair.y));
                }
            } else if (pair.y.equals(toReplaceVar)) {
                newAllocMem.set(i, new LLVMAllocation(pair.x, replacementVar));
            }
        }
        // associations
        Map<LLVMHeuristicVariable, Integer> newAssocs =
            new LinkedHashMap<LLVMHeuristicVariable, Integer>(this.getAssociations());
        Map<LLVMHeuristicVariable, BigInteger> newAssocOffsets =
            new LinkedHashMap<LLVMHeuristicVariable, BigInteger>(this.getAssociationOffsets());
        if (newAssocs.containsKey(toReplaceVar)) {
            if (Globals.useAssertions) {
                if (newAssocs.containsKey(replacementVar)) {
                    assert (newAssocs.get(toReplaceVar).equals(newAssocs.get(replacementVar))) :
                        "Trying to replace references from different allocated areas!";
                }
            }
            newAssocs.put(replacementVar, newAssocs.remove(toReplaceVar));
            BigInteger offset = newAssocOffsets.get(replacementVar);
            newAssocOffsets.put(
                replacementVar,
                offset == null ? newAssocOffsets.remove(toReplaceVar) : offset.max(newAssocOffsets.remove(toReplaceVar))
            );
        }
        // call stack
        Deque<LLVMReturnInformation> newCallStack = new ArrayDeque<LLVMReturnInformation>();
        for (LLVMReturnInformation inf : this.getCallStack()) {
            Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVarFunc =
                new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>(inf.getProgramVariables());
            for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> e : newVarFunc.entrySet()) {
                if (e.getValue().x.equals(toReplaceVar)) {
                    e.setValue(new ImmutablePair<LLVMSymbolicVariable, LLVMType>(replacementVar, e.getValue().y));
                }
            }
            newCallStack.add(
                new LLVMReturnInformation(
                    ImmutableCreator.create(newVarFunc),
                    inf.getProgPos(),
                    inf.getAllocationsInFunction()
                )
            );
        }
        // cache for unequal references
        Set<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> newUnequalCache =
            new LinkedHashSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>>();
        for (ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef> unequal : this.getUnequalCache()) {
            if (unequal.x.equals(toReplaceVar)) {
                if (replacementVar instanceof LLVMHeuristicVarRef) {
                    newUnequalCache.add(
                        new ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>(
                            (LLVMHeuristicVarRef)replacementVar,
                            unequal.y
                        )
                    );
                }
            } else if (unequal.y.equals(toReplaceVar)) {
                if (replacementVar instanceof LLVMHeuristicVarRef) {
                    newUnequalCache.add(
                        new ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>(
                            unequal.x,
                            (LLVMHeuristicVarRef)replacementVar
                        )
                    );
                }
            } else {
                newUnequalCache.add(unequal);
            }
        }
        // initial heap references
        Map<Integer, LLVMHeuristicVariable> newInitHeapRefs =
            new LinkedHashMap<Integer, LLVMHeuristicVariable>(this.getInitialHeapAddresses());
        for (Map.Entry<Integer, LLVMHeuristicVariable> entry : newInitHeapRefs.entrySet()) {
            if (entry.getValue().equals(toReplaceVar)) {
                entry.setValue(replacementVar);
            }
        }
        return
            new LLVMHeuristicIntegerState(
                ImmutableCreator.create(newRels),
                ImmutableCreator.create(newVals),
                ImmutableCreator.create(newUnequalCache),
                ImmutableCreator.create(newVars),
                ImmutableCreator.create(newHeap),
                ImmutableCreator.create(newAllocMem),
                ImmutableCreator.create(newAssocs),
                ImmutableCreator.create(newAssocOffsets),
                ImmutableCreator.create(newCallStack),
                ImmutableCreator.create(newInitHeapRefs),
                false,
                false,
                this.params
            );
    }

    /**
     * @param adjustedParam Have the values been adjusted?
     * @return This state where the adjusted flag has been set to the specified value.
     */
    public LLVMHeuristicIntegerState setAdjusted(boolean adjustedParam) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                this.isClean(),
                adjustedParam,
                this.params
            );
    }

    /**
     * @param newAllocs The new allocations.
     * @return This heuristic integer state where the allocations are set to the specified ones.
     */
    @Override
    public LLVMHeuristicIntegerState setAllocations(List<LLVMAllocation> newAllocs) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                ImmutableCreator.create(newAllocs),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                this.isAdjusted(),
                this.params
            );
    }

    /**
     * @param newAssocOffsets The new association offsets.
     * @return This heuristic integer state where the association offsets are set to the specified ones.
     */
    public LLVMHeuristicIntegerState setAssociationOffsets(Map<LLVMHeuristicVariable, BigInteger> newAssocOffsets) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                ImmutableCreator.create(newAssocOffsets),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    /**
     * @param newAssocs The new associations.
     * @return This heuristic integer state where the associations are set to the specified ones.
     */
    public LLVMHeuristicIntegerState setAssociations(Map<LLVMHeuristicVariable, Integer> newAssocs) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                ImmutableCreator.create(newAssocs),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    /**
     * @param newCallStack The new call stack.
     * @return A state with the specified call stack and everything else as in the current state.
     */
    public LLVMHeuristicIntegerState setCallStack(Deque<LLVMReturnInformation> newCallStack) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                ImmutableCreator.create(newCallStack),
                this.getInitialHeapAddresses(),
                this.isClean(),
                this.isAdjusted(),
                this.params
            );
    }

    /**
     * @param cleanParam Are the relation clean?
     * @return This state where the clean flag has been set to the specified value.
     */
    public LLVMHeuristicIntegerState setClean(boolean cleanParam) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                cleanParam,
                this.isAdjusted(),
                this.params
            );
    }

    /**
     * @param newInitHeapAddrs The new initial heap addresses.
     * @return A state with the specified initial heap addresses and everything else as in the current state.
     */
    public LLVMHeuristicIntegerState setInitialHeapAddresses(Map<Integer, LLVMHeuristicVariable> newInitHeapAddrs) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                ImmutableCreator.create(newInitHeapAddrs),
                this.isClean(),
                this.isAdjusted(),
                this.params
            );
    }

    @Override
    public LLVMHeuristicIntegerState setMemory(Map<LLVMMemoryRange, LLVMMemoryInvariant> newMemory) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                ImmutableCreator.create(newMemory),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    /**
     * @param vars The new program variable function.
     * @return This state with the specified program variable function instead of its current one.
     */
    public LLVMHeuristicIntegerState setProgramVariables(
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> vars
    ) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                this.getUnequalCache(),
                ImmutableCreator.create(vars),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                this.isClean(),
                this.isAdjusted(),
                this.params
            );
    }

    /**
     * @param newRels The new relation set.
     * @return This state where the relation set has been set to the specified one.
     */
    public LLVMHeuristicIntegerState setRelations(Set<LLVMHeuristicRelation> newRels) {
        return
            new LLVMHeuristicIntegerState(
                ImmutableCreator.create(newRels),
                this.getValues(),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    /**
     * @param newUnequalCache The new cache for unequal variables.
     * @return This state where the cache for unequal variables has been set to the specified one.
     */
    public LLVMHeuristicIntegerState setUnequalCache(
        Set<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> newUnequalCache
    ) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                this.getValues(),
                ImmutableCreator.create(newUnequalCache),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    /**
     * @param ref The reference to map.
     * @param val The value to map the reference to.
     * @return An AbstractState with the new value mapping, but everything else as in the current state.
     */
    public LLVMHeuristicIntegerState setValue(LLVMHeuristicVariable ref, LLVMValue val) {
        if (ref.isConcrete()) {
            if (Globals.useAssertions) {
                assert (val.isIntLiteral()) : "Tried to set a non-constant value for a constant reference!";
                assert (val.getIntLiteralValue() != null) :
                    "Although we have a constant, we cannot get its value...";
                assert (val.getIntLiteralValue().equals(((LLVMHeuristicConstRef)ref).getIntegerValue())) :
                    "Tried to replace a constant by another constant!";
            }
            return this;
        } else {
            Map<LLVMHeuristicVariable, LLVMValue> newVals =
                new LinkedHashMap<LLVMHeuristicVariable, LLVMValue>(this.getValues());
            newVals.put(ref, val);
            return this.setValues(newVals);
        }
    }

    /**
     * @param newValues The new values.
     * @return This state where the values have been set to the specified ones.
     */
    public LLVMHeuristicIntegerState setValues(Map<LLVMHeuristicVariable, LLVMValue> newValues) {
        return
            new LLVMHeuristicIntegerState(
                this.getRelations(),
                ImmutableCreator.create(newValues),
                this.getUnequalCache(),
                this.getProgramVariables(),
                this.getMemory(),
                this.getAllocations(),
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getCallStack(),
                this.getInitialHeapAddresses(),
                false,
                false,
                this.params
            );
    }

    @Override
    public String toDOTString() {
        StringBuilder strBuilder = new StringBuilder();
        final Comparator<String> nameComp = new Comparator<String>() {

            @Override
            public int compare(String o1, String o2) {
                if ((o1.startsWith("%") && o2.startsWith("%")) || (o1.startsWith("v") && o2.startsWith("v"))) {
                    try {
                        return
                            Integer.compare(Integer.parseInt(o1.substring(1)), Integer.parseInt(o2.substring(1)));
                    } catch (NumberFormatException e) {
                        // do nothing
                    }
                }
                return o1.compareTo(o2);
            }

        };
        final Comparator<LLVMHeuristicVariable> refComp = new Comparator<LLVMHeuristicVariable>() {

            @Override
            public int compare(LLVMHeuristicVariable o1, LLVMHeuristicVariable o2) {
                return nameComp.compare(o1.getName(), o2.getName());
            }

        };
        Comparator<LLVMHeuristicRelation> relComp = new Comparator<LLVMHeuristicRelation>() {

            @Override
            public int compare(LLVMHeuristicRelation o1, LLVMHeuristicRelation o2) {
                List<LLVMHeuristicVariable> refList1 = new ArrayList<LLVMHeuristicVariable>(o1.getVariables(false));
                List<LLVMHeuristicVariable> refList2 = new ArrayList<LLVMHeuristicVariable>(o2.getVariables(false));
                if (refList1.isEmpty()) {
                    if (refList2.isEmpty()) {
                        return 0;
                    }
                    return -1;
                } else if (refList2.isEmpty()) {
                    return 1;
                }
                Collections.sort(refList1, refComp);
                Collections.sort(refList2, refComp);
                return refComp.compare(refList1.get(0), refList2.get(0));
            }

        };
        strBuilder.append("vals:\\n");
        strBuilder.append(DOTFormatter.toDOT(this.getValues(), "=", DOTFormatter.BIG_DOT_NL_LIMIT, refComp));
        strBuilder.append("\\nassociations:\\n");
        strBuilder.append(
            DOTFormatter.<LLVMHeuristicVariable, BigInteger>toDOT(
                this.getAssociations(),
                this.getAssociationOffsets(),
                this.getAllocations(),
                "in",
                DOTFormatter.BIG_DOT_NL_LIMIT,
                refComp
            )
        );
        LLVMHeuristicRelationSet rels = new LLVMHeuristicRelationSet(this.getRelations());
        strBuilder.append("\\nrels:\\nundirected inequalities:\\n");
        strBuilder.append(
            DOTFormatter.toDOT(rels.getUndirectedInequalities(), DOTFormatter.BIG_DOT_NL_LIMIT, relComp)
        );
        strBuilder.append("\\nequations:\\n");
        strBuilder.append(DOTFormatter.toDOT(rels.getEquations(), DOTFormatter.BIG_DOT_NL_LIMIT, relComp));
        strBuilder.append("\\nweak directed inequalities:\\n");
        strBuilder.append(
            DOTFormatter.toDOT(rels.getWeakDirectedInequalities(), DOTFormatter.BIG_DOT_NL_LIMIT, relComp)
        );
        strBuilder.append("\\nstrict directed inequalities:\\n");
        strBuilder.append(
            DOTFormatter.toDOT(rels.getStrictDirectedInequalities(), DOTFormatter.BIG_DOT_NL_LIMIT, relComp)
        );
        return strBuilder.toString();
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", "LLVMHeuristicIntegerState");
        res.put("values", JSONExportUtil.toJSON(this.getValues()));
        res.put("relations", JSONExportUtil.toJSON(this.getRelations()));
        res.put("assocs", JSONExportUtil.toJSON(this.getAssociations()));
        res.put("assoc_offsets", JSONExportUtil.toJSON(this.getAssociationOffsets()));
        res.put("initial_heap", JSONExportUtil.toJSON(this.getInitialHeapAddresses()));
        res.put("unequal_cache", JSONExportUtil.toJSON(this.getUnequalCache()));
        return res;
    }

    @Override
    public IntegerRelationSet toRelationSet() {
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        final IntegerRelationSet res = new IntegerRelationSet(this.getRelations());
        for (Map.Entry<LLVMHeuristicVariable, LLVMValue> entry : this.getValues().entrySet()) {
            if (entry.getValue() instanceof AbstractFloat) continue;
            final LLVMHeuristicVariable var = entry.getKey();
            final AbstractBoundedInt value = entry.getValue().getThisAsAbstractBoundedInt();
            final IntervalBound lower = value.getLower();
            final IntervalBound upper = value.getUpper();
            if (lower.isFinite()) {
                res.add(relationFactory.lessThanEquals(termFactory.constant(lower.getConstant()), var));
            }
            if (upper.isFinite()) {
                res.add(relationFactory.lessThanEquals(var, termFactory.constant(upper.getConstant())));
            }
            if (value.containsLiteral(-1) && value.containsLiteral(1) && !value.containsLiteral(0)) {
                res.add(relationFactory.notEqualTo(var, termFactory.zero()));
            }
        }
        for (LLVMAllocation allocation : this.getAllocations()) {
            res.add(relationFactory.lessThanEquals(termFactory.one(), allocation.x));
            res.add(relationFactory.lessThanEquals(allocation.x, allocation.y));
        }
        return res;
    }

    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("vals:\n");
        strBuilder.append(this.getValues());
        strBuilder.append("\nassociations:\n");
        strBuilder.append(this.getAssociations());
        strBuilder.append("\nassociation offsets:\n");
        strBuilder.append(this.getAssociationOffsets());
        LLVMHeuristicRelationSet rels = new LLVMHeuristicRelationSet(this.getRelations());
        strBuilder.append("\nrels:\nundirected inequalities:\n");
        strBuilder.append(rels.getUndirectedInequalities());
        strBuilder.append("\nequations:\n");
        strBuilder.append(rels.getEquations());
        strBuilder.append("\nweak directed inequalities:\n");
        strBuilder.append(rels.getWeakDirectedInequalities());
        strBuilder.append("\nstrict directed inequalities:\n");
        strBuilder.append(rels.getStrictDirectedInequalities());
        return strBuilder.toString();
    }

    /**
     * Checks for an inner bound relation modOp <= rhs, where modOp is a modulo operation, if it holds or not.
     * @param state The abstract state containing the information about the references and the known relations.
     * @param modOp TODO
     * @param rhs TODO
     * @return YES if the relation holds, NO if its inverse holds, and MAYBE if we just do not know.
     */
    public YNM truthValueOfInnerBoundRelation(LLVMHeuristicOperation modOp, LLVMHeuristicConstRef rhs) {
        if (modOp.isModuloOperation() && modOp.getRhs() instanceof LLVMHeuristicConstRef) {
            // we have a relation of the form expr mod c <= rhs, where c and rhs are constants
            LLVMHeuristicConstRef c = (LLVMHeuristicConstRef)modOp.getRhs();
            LLVMHeuristicVariable ref;
            LLVMHeuristicConstRef offset;
            if (modOp.getLhs() instanceof LLVMHeuristicVariable) {
                ref = (LLVMHeuristicVariable)modOp.getLhs();
                offset = this.getRelationFactory().getTermFactory().zero();
            } else if (modOp.getLhs() instanceof LLVMHeuristicOperation) {
                LLVMHeuristicOperation modOpLhs = (LLVMHeuristicOperation) modOp.getLhs();
                if (
                    modOpLhs.getLhs() instanceof LLVMHeuristicVarRef
                    && modOpLhs.getRhs() instanceof LLVMHeuristicConstRef
                ) {
                    ref = (LLVMHeuristicVariable)modOpLhs.getLhs();
                    if (modOpLhs.getOperation().equals(ArithmeticOperationType.ADD)) {
                        offset = (LLVMHeuristicConstRef)modOpLhs.getRhs();
                    } else if (modOpLhs.getOperation().equals(ArithmeticOperationType.SUB)) {
                        offset = (LLVMHeuristicConstRef)modOpLhs.getRhs().negate();
                    } else {
                        return YNM.MAYBE;
                    }
                } else if (
                    modOpLhs.getLhs() instanceof LLVMHeuristicConstRef
                    && modOpLhs.getRhs() instanceof LLVMHeuristicVarRef
                ) {
                    ref = (LLVMHeuristicVariable)modOpLhs.getRhs();
                    if (modOpLhs.getOperation().equals(ArithmeticOperationType.ADD)) {
                        offset = (LLVMHeuristicConstRef)modOpLhs.getLhs();
                    } else {
                        return YNM.MAYBE;
                    }
                } else {
                    return YNM.MAYBE;
                }
            } else {
                return YNM.MAYBE;
            }
            // we have a relation of the form (ref + offset) mod c <= rhs, where c and rhs are constants
            AbstractBoundedInt valOfRef = this.getValue(ref).getThisAsAbstractBoundedInt();
            BigInteger valOfC = c.getIntegerValue();
            BigInteger valOfRhs = rhs.getIntegerValue();
            BigInteger valOfOffset = offset.getIntegerValue();
            BigInteger refLB = valOfRef.getLower().getConstant();
            BigInteger refUB = valOfRef.getUpper().getConstant();
            if (
                (refLB.compareTo(BigInteger.ZERO) >= 0 || refLB.multiply(BigInteger.valueOf(-2)).compareTo(valOfC) <= 0)
                && (
                    refUB.compareTo(BigInteger.ZERO) <= 0
                    || refUB.add(BigInteger.ONE).multiply(BigInteger.valueOf(2)).compareTo(valOfC) <= 0
                )
            ) {
                // we have an inner bound relation:
                // ((ref + offset) mod c <= rhs) implies (ref <= rhs - offset - c) or (ref >= -offset)
                // -> check if either (ref <= rhs - offset - c) or (ref >= -offset) holds
                BigInteger innerUB = valOfRhs.subtract(valOfOffset).subtract(valOfC);
                BigInteger innerLB = valOfOffset.negate();
                if (refLB.compareTo(innerLB) >= 0 || refUB.compareTo(innerUB) <= 0) {
                    return YNM.YES;
                }
                if (refLB.compareTo(innerUB) > 0 && refUB.compareTo(innerLB) < 0) {
                    return YNM.NO;
                }
            }
        }
        return YNM.MAYBE;
    }

    /**
     * @param state The integer state containing the information about the references and the known relations.
     * @param rel The relation to check.
     * @param useCache Should we use the cache?
     * @return YES if the relation holds, NO if its inverse holds, and MAYBE if we just do not know.
     */
    public YNM truthValueOfRelation(LLVMHeuristicRelation rel, boolean useCache, Abortion aborter) {
        return this.truthValueOfRelation(rel.getLhs(), rel.getHeuristicRelationType(), rel.getRhs(), useCache, aborter);
    }

    /**
     * @param state The abstract state holding the knowledge about the references.
     * @param knownRelations The known relations.
     * @param firstExpr The first expression.
     * @param relType The relation type.
     * @param secondExpr The second expression.
     * @param useCache Should we use the cache?
     * @param params Strategy parameters.
     * @return YES if the relation firstExpr relType secondExpr holds, NO if its inverse holds, and MAYBE if we just do
     *         not know.
     */
    public YNM truthValueOfRelation(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicRelationType relType,
        LLVMHeuristicTerm secondExpr,
        boolean useCache,
        Abortion aborter
    ) {
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final IntegerRelationType relTypeGeneral = relType.toIntegerRelationType();
        if (firstExpr.equals(secondExpr)) {
            return LLVMHeuristicIntegerState.truthValueForEqualExpressions(relTypeGeneral);
        }
        IntegerRelationType relTypeInverted = relTypeGeneral.invert();
        final Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> simpleRelation =
            this.toSimpleRelation(firstExpr, secondExpr);
        if (simpleRelation != null) {
            YNM refRes =
                this.truthValueOfSimpleRelation(
                    knownRelations,
                    simpleRelation.x,
                    simpleRelation.y,
                    relTypeGeneral,
                    relTypeInverted,
                    useCache
                );
            if (refRes != YNM.MAYBE) {
                return refRes;
            }
        }
        if (
            firstExpr instanceof LLVMHeuristicOperation
            && ((LLVMHeuristicOperation)firstExpr).isModuloOperation()
            && relType == LLVMHeuristicRelationType.LE
            && secondExpr instanceof LLVMHeuristicConstRef
        ) {
            YNM refRes =
                this.truthValueOfInnerBoundRelation(
                    (LLVMHeuristicOperation)firstExpr,
                    (LLVMHeuristicConstRef)secondExpr
                );
            if (refRes != YNM.MAYBE) {
                return refRes;
            }
        }
//        if (
//            secondExpr instanceof LLVMHeuristicOperation
//            && ((LLVMHeuristicOperation)secondExpr).isModuloOperation()
//            && relType.equals(IntegerRelationType.GE)
//            && firstExpr instanceof LLVMHeuristicConstRef) {
//            YNM refRes =
//                LLVMHeuristicIntegerState.truthValueOfInnerBoundRelation(
//                    this.state,
//                    (LLVMHeuristicOperation)secondExpr,
//                    (LLVMHeuristicConstRef)firstExpr
//                );
//            if (refRes != YNM.MAYBE) {
//                return refRes;
//            }
//        }
        LLVMHeuristicRelation checkedRel = relationFactory.createRelation(relType, firstExpr, secondExpr);
        LLVMHeuristicRelation checkedRelInverted =
            relationFactory.createRelation(relTypeInverted, firstExpr, secondExpr);
        // Is the relation contained as it is?
        if (knownRelations.contains(checkedRel)) {
            return YNM.YES;
        }
        if (knownRelations.contains(checkedRelInverted)) {
            return YNM.NO;
        }
        if (LLVMDebuggingFlags.DUMP_SMTLIB) {
            try (FileWriter writer = new FileWriter(LLVMDebuggingFlags.getNextSMTLIBDumpFile())) {
                this.dumpSMTLIB(
                    LLVMHeuristicIntegerState.dumperFactory.getDumper(writer, SMTLIBLogic.QF_NIA, aborter),
                    knownRelations,
                    checkedRel
                );
            } catch (IOException e) {
                e.printStackTrace(System.err);
            }
        }
        long time = System.currentTimeMillis();
        ++LLVMHeuristicRelationSet.smtCalls;
        boolean strict;
        boolean greater;
        boolean directedInequality;
        switch (relType) {
            case LE:
                strict = false;
                greater = false;
                directedInequality = true;
                break;
            case LT:
                strict = true;
                greater = false;
                directedInequality = true;
                break;
//            case GE:
//                strict = false;
//                greater = true;
//                directedInequality = true;
//                break;
//            case GT:
//                strict = true;
//                greater = true;
//                directedInequality = true;
//                break;
            default:
                strict = false;
                greater = false;
                directedInequality = false;
        }
        if (directedInequality) {
            YNM directedResult =
                this.handleDirectedInequality(
                    knownRelations,
                    firstExpr,
                    secondExpr,
                    strict,
                    greater,
                    aborter
                );
            if (directedResult != YNM.MAYBE) {
                LLVMHeuristicRelationSet.smtSolving += System.currentTimeMillis() - time;
                return directedResult;
            }
        } else {
            // we must have EQ or NE
            boolean equal = relType == LLVMHeuristicRelationType.EQ;
            if (equal) {
                YNM aligned =
                    LLVMHeuristicIntegerState.truthValueOfAlignmentRelation(
                        knownRelations,
                        firstExpr,
                        secondExpr,
                        useCache
                    );
                if (aligned != YNM.MAYBE) {
                    LLVMHeuristicRelationSet.smtSolving += System.currentTimeMillis() - time;
                    return aligned;
                }
            }
            // we can check whether we can infer a strict directed inequality - this would answer our question
            YNM lt =
                this.truthValueOfRelation(
                    knownRelations,
                    firstExpr,
                    LLVMHeuristicRelationType.LT,
                    secondExpr,
                    useCache,
                    aborter
                );
            if (lt == YNM.YES) {
                LLVMHeuristicRelationSet.smtSolving += System.currentTimeMillis() - time;
                return equal ? YNM.NO : YNM.YES;
            } else if (lt == YNM.NO) {
                YNM gt =
                    this.truthValueOfRelation(
                        knownRelations,
                        secondExpr,
                        LLVMHeuristicRelationType.LT,
                        firstExpr,
                        useCache,
                        aborter
                    );
                if (gt != YNM.MAYBE) {
                    LLVMHeuristicRelationSet.smtSolving += System.currentTimeMillis() - time;
                    return equal ? YNM.invert(gt) : gt;
                }
                // else fall through to MAYBE
            }
        }
        LLVMHeuristicRelationSet.smtSolving += System.currentTimeMillis() - time;
        return YNM.MAYBE;
    }

    /**
     * @param state The abstract state containing the information about the references and the known relations.
     * @param firstExpr The first expression.
     * @param relType The relation between the two expressions, i.e., we consider
     *                <code>firstExpr</code> <code>relType</code> <code>secondExpr</code>.
     * @param secondExpr The second expression.
     * @param useCache Should we use the cache?
     * @param params Strategy parameters.
     * @return YES if the relation holds, NO if its inverse holds, and MAYBE if we just do not know.
     */
    public YNM truthValueOfRelation(
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicRelationType relType,
        LLVMHeuristicTerm secondExpr,
        boolean useCache,
        Abortion aborter
    ) {
        return
            this.truthValueOfRelation(
                new LLVMHeuristicRelationSet(this.getRelations()),
                firstExpr,
                relType,
                secondExpr,
                useCache,
                aborter
            );
    }

    @Override
    protected LLVMHeuristicRelationFactory getRelationFactory() {
        return LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY;
    }

    @Override
    protected SMTSolver getSolver(Abortion aborter) {
        // not used
        return null;
    }

    /**
     * Check for a strict inequality in the transitive closure of our relations.
     * @param state The abstract state holding the knowledge about the references.
     * @param knownRelations The known relations.
     * @param firstExpr The first expression.
     * @param secondExpr The second expression.
     * @param greater Flag indicating whether we look for a relation firstExpr > secondExpr (true) or
     *                firstExpr < secondExpr (false).
     * @param params Strategy parameters.
     * @return YES, if we find out that the known relations imply the desired relation, NO if we find out that they
     *         imply the corresponding inverse relation, and MAYBE otherwise.
     */
    private YNM checkForStrictInequalityInTransitiveClosure(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicTerm secondExpr,
        boolean greater,
        Abortion aborter
    ) {
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> secondLinear = secondExpr.toLinear();
        if (firstExpr.toLinear().x == null || secondLinear.x == null) {
            // at least one expression is a constant - there is no need for further checking
            return YNM.MAYBE;
        }
        // we look for a strict relation - first set up everything we need
        ImmutableList<LLVMAllocation> allocations = this.getAllocations();
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs = this.getAssociations();
        ImmutableMap<LLVMHeuristicVariable, BigInteger> assocOffsets = this.getAssociationOffsets();
        Map<LLVMAllocation, Set<LLVMHeuristicVariable>> associationsInverse =
            LLVMHeuristicIntegerState.buildInverseAssociations(allocations, assocs);
        ImmutableMap<LLVMHeuristicVariable, LLVMValue> vals = this.getValues();
        LLVMHeuristicRelationSet usefulRels =
            LLVMHeuristicIntegerState.computeUsefulRels(
                knownRelations,
                allocations,
                assocs,
                associationsInverse,
                firstExpr,
                secondExpr
            );
        if (usefulRels == null) {
            return YNM.MAYBE;
        }
        // contains expressions x known to satisfy (firstExpr greater ? >= : <=) x
        // we just need one strict step from here
        Set<LLVMHeuristicTerm> weak = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> lastWeak = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> newWeak = new LinkedHashSet<LLVMHeuristicTerm>();
        // contains expressions x known to satisfy (firstExpr greater ? <= : >=) x
        // the inverse could also hold
        Set<LLVMHeuristicTerm> weakInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> lastWeakInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> newWeakInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        newWeak.add(firstExpr);
        newWeakInverse.add(firstExpr);
        // contains expressions x known to satisfy (firstExpr greater ? > : <) x
        Set<LLVMHeuristicTerm> strict = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> lastStrict = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> newStrict = new LinkedHashSet<LLVMHeuristicTerm>();
        int maxNumOfVarOccs = usefulRels.computeMaximalNumberOfVariableOccurrences();
        maxNumOfVarOccs = Math.max(maxNumOfVarOccs, firstExpr.getNumberOfVarOccs());
        maxNumOfVarOccs = Math.max(maxNumOfVarOccs, secondExpr.getNumberOfVarOccs());
        // we need one less as at least one variable is always resolved
        maxNumOfVarOccs--;
        BigInteger highestFactor = usefulRels.computeHighestAbsoluteFactor();
        highestFactor = highestFactor.max(firstExpr.computeHighestAbsoluteFactor());
        highestFactor = highestFactor.max(secondExpr.computeHighestAbsoluteFactor());
        Set<Pair<LLVMHeuristicVariable, BigInteger>> arrayPatterns =
            LLVMHeuristicIntegerState.computeArrayPatterns(usefulRels, firstExpr, secondExpr);
        while (!newWeak.isEmpty() || !newStrict.isEmpty() || !newWeakInverse.isEmpty()) {
            aborter.checkAbortion();
            strict.addAll(newStrict);
            weakInverse.addAll(newWeakInverse);
            weak.addAll(newWeak);
            lastWeak.clear();
            lastWeak.addAll(newWeak);
            newWeak.clear();
            lastStrict.clear();
            lastStrict.addAll(newStrict);
            newStrict.clear();
            lastWeakInverse.clear();
            lastWeakInverse.addAll(newWeakInverse);
            newWeakInverse.clear();
            for (LLVMHeuristicRelation rel : usefulRels) {
                for (LLVMHeuristicTerm expr : lastWeak) {
                    newStrict.addAll(
                        rel.getExpressionsInDirectedInequality(this, knownRelations, expr, true, greater, this.params, aborter)
                    );
                    newWeak.addAll(
                        rel.getExpressionsInDirectedInequality(this, knownRelations, expr, false, greater, this.params, aborter)
                    );
                }
                for (LLVMHeuristicTerm expr : lastStrict) {
                    newStrict.addAll(
                        rel.getExpressionsInDirectedInequality(this, knownRelations, expr, false, greater, this.params, aborter)
                    );
                }
                for (LLVMHeuristicTerm expr : lastWeakInverse) {
                    newWeakInverse.addAll(
                        rel.getExpressionsInDirectedInequality(
                            this,
                            knownRelations,
                            expr,
                            false,
                            !greater,
                            this.params,
                            aborter
                        )
                    );
                }
            }
//            System.err.println("Go here for debugging!");
            this.handleAllocationsAndAssociations(
                allocations,
                assocs,
                assocOffsets,
                associationsInverse,
                new Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>>(lastWeak, newWeak),
                new Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>>(lastStrict, newStrict),
                new Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>>(lastWeakInverse, newWeakInverse),
                greater
            );
//            System.err.println("Go here for debugging!");
            LLVMHeuristicIntegerState.handleValues(vals, newWeak, newWeak, false, greater);
            LLVMHeuristicIntegerState.handleValues(vals, newWeak, newStrict, true, greater);
            LLVMHeuristicIntegerState.handleValues(vals, newStrict, newStrict, false, greater);
            LLVMHeuristicIntegerState.handleValues(vals, newWeakInverse, newWeakInverse, false, !greater);
            YNM intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    newStrict,
                    newWeak,
                    true,
                    true,
                    greater,
                    secondLinear,
                    true,
                    true
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
            intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    strict,
                    newWeak,
                    true,
                    true,
                    greater,
                    secondLinear,
                    true,
                    true
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
            intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    weak,
                    newWeak,
                    false,
                    true,
                    greater,
                    secondLinear,
                    true,
                    true
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
            intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    strict,
                    newStrict,
                    false,
                    false,
                    greater,
                    secondLinear,
                    true,
                    false
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
            intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    weakInverse,
                    newWeakInverse,
                    false,
                    false,
                    !greater,
                    secondLinear,
                    false,
                    false
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
        }
        // the offset of secondExpr must limit the offset of the found expression in the other direction (the sets go
        // away from firstExpr towards secondExpr)
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = secondExpr.toLinear();
        if (linear.x != null) {
            for (LLVMHeuristicTerm strictExpr : strict) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> strictLinear = strictExpr.toLinear();
                if (
                    linear.x.equals(strictLinear.x)
                    && linear.z.compareTo(strictLinear.z) == 0
                    && LLVMHeuristicIntegerState.isInRelation(strictLinear.y, linear.y, false, greater)
                ) {
                    return YNM.YES;
                }
            }
            for (LLVMHeuristicTerm weakExpr : weak) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> weakLinear = weakExpr.toLinear();
                if (
                    linear.x.equals(weakLinear.x)
                    && linear.z.compareTo(weakLinear.z) == 0
                    && LLVMHeuristicIntegerState.isInRelation(weakLinear.y, linear.y, true, greater)
                ) {
                    return YNM.YES;
                }
            }
            for (LLVMHeuristicTerm weakInvExpr : weakInverse) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> invLinear = weakInvExpr.toLinear();
                if (
                    linear.x.equals(invLinear.x)
                    && linear.z.compareTo(invLinear.z) == 0
                    && LLVMHeuristicIntegerState.isInRelation(invLinear.y, linear.y, false, !greater)
                ) {
                    return YNM.NO;
                }
            }
        }
        return YNM.MAYBE;
    }

    /**
     * Check for a weak inequality in the transitive closure of our relations.
     * @param state The abstract state holding the knowledge about the references.
     * @param knownRelations The known relations.
     * @param firstExpr The first expression.
     * @param secondExpr The second expression.
     * @param greater Flag indicating whether we look for a relation firstExpr >= secondExpr (true) or
     *                firstExpr <= secondExpr (false).
     * @param params Strategy parameters.
     * @return YES, if we find out that the known relations imply the desired relation, NO if we find out that they
     *         imply the corresponding inverse relation, and MAYBE otherwise.
     */
    private YNM checkForWeakInequalityInTransitiveClosure(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicTerm secondExpr,
        boolean greater,
        Abortion aborter
    ) {
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> secondLinear = secondExpr.toLinear();
        if (firstExpr.toLinear().x == null || secondLinear.x == null) {
            // at least one expression is a constant - for unbounded integers, there is no need for further checking
            if (!this.params.useBoundedIntegers) {
                return YNM.MAYBE;
            }
        }
        // we look for a weak relation - first set up everything we need
        ImmutableList<LLVMAllocation> allocations = this.getAllocations();
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs = this.getAssociations();
        ImmutableMap<LLVMHeuristicVariable, BigInteger> assocOffsets = this.getAssociationOffsets();
        Map<LLVMAllocation, Set<LLVMHeuristicVariable>> associationsInverse =
            LLVMHeuristicIntegerState.buildInverseAssociations(allocations, assocs);
        ImmutableMap<LLVMHeuristicVariable, LLVMValue> vals = this.getValues();
        // we only need equations and directed inequalities with at least two references which might contribute to the
        // relation we are looking for
        LLVMHeuristicRelationSet usefulRels =
            LLVMHeuristicIntegerState.computeUsefulRels(
                knownRelations,
                allocations,
                assocs,
                associationsInverse,
                firstExpr,
                secondExpr
            );
        if (usefulRels == null) {
            return YNM.MAYBE;
        }
        // contains expressions x known to satisfy firstExpr (greater ? >= : <=) x, that's what we look for
        Set<LLVMHeuristicTerm> weak = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> lastWeak = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> newWeak = new LinkedHashSet<LLVMHeuristicTerm>();
        // contains expressions x known to satisfy firstExpr (greater ? <= : >=) x
        // we just need one strict step from here for the inverse
        Set<LLVMHeuristicTerm> weakInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> lastWeakInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> newWeakInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        newWeak.add(firstExpr);
        newWeakInverse.add(firstExpr);
        // contains expressions x known to satisfy firstExpr (greater ? < : >) x
        Set<LLVMHeuristicTerm> strictInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> lastStrictInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        Set<LLVMHeuristicTerm> newStrictInverse = new LinkedHashSet<LLVMHeuristicTerm>();
        int maxNumOfVarOccs = usefulRels.computeMaximalNumberOfVariableOccurrences();
        maxNumOfVarOccs = Math.max(maxNumOfVarOccs, firstExpr.getNumberOfVarOccs());
        maxNumOfVarOccs = Math.max(maxNumOfVarOccs, secondExpr.getNumberOfVarOccs());
        // we need one less as at least one variable is always resolved
        maxNumOfVarOccs--;
        BigInteger highestFactor = usefulRels.computeHighestAbsoluteFactor();
        highestFactor = highestFactor.max(firstExpr.computeHighestAbsoluteFactor());
        highestFactor = highestFactor.max(secondExpr.computeHighestAbsoluteFactor());
        Set<Pair<LLVMHeuristicVariable, BigInteger>> arrayPatterns =
            LLVMHeuristicIntegerState.computeArrayPatterns(usefulRels, firstExpr, secondExpr);
        while (!newWeak.isEmpty() || !newWeakInverse.isEmpty() || !newStrictInverse.isEmpty()) {
            aborter.checkAbortion();
            weak.addAll(newWeak);
            strictInverse.addAll(newStrictInverse);
            weakInverse.addAll(newWeakInverse);
            lastWeak.clear();
            lastWeak.addAll(newWeak);
            newWeak.clear();
            lastWeakInverse.clear();
            lastWeakInverse.addAll(newWeakInverse);
            newWeakInverse.clear();
            lastStrictInverse.clear();
            lastStrictInverse.addAll(newStrictInverse);
            newStrictInverse.clear();
            for (LLVMHeuristicRelation rel : usefulRels) {
//                System.err.println("Go here for debugging!");
                for (LLVMHeuristicTerm expr : lastWeak) {
                    newWeak.addAll(
                        rel.getExpressionsInDirectedInequality(this, usefulRels, expr, false, greater, this.params, aborter)
                    );
                }
                for (LLVMHeuristicTerm expr : lastWeakInverse) {
                    newStrictInverse.addAll(
                        rel.getExpressionsInDirectedInequality(
                            this,
                            usefulRels,
                            expr,
                            true,
                            !greater,
                            this.params,
                            aborter
                        )
                    );
                    newWeakInverse.addAll(
                        rel.getExpressionsInDirectedInequality(
                            this,
                            usefulRels,
                            expr,
                            false,
                            !greater,
                            this.params, 
                            aborter
                        )
                    );
                }
                for (LLVMHeuristicTerm expr : lastStrictInverse) {
                    newStrictInverse.addAll(
                        rel.getExpressionsInDirectedInequality(
                            this,
                            usefulRels,
                            expr,
                            false,
                            !greater,
                            this.params,
                            aborter
                        )
                    );
                }
            }
//            System.err.println("Go here for debugging!");
            this.handleAllocationsAndAssociations(
                allocations,
                assocs,
                assocOffsets,
                associationsInverse,
                new Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>>(lastWeakInverse, newWeakInverse),
                new Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>>(lastStrictInverse, newStrictInverse),
                new Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>>(lastWeak, newWeak),
                !greater
            );
//            System.err.println("Go here for debugging!");
            LLVMHeuristicIntegerState.handleValues(vals, newWeak, newWeak, false, greater);
            LLVMHeuristicIntegerState.handleValues(vals, newWeakInverse, newWeakInverse, false, !greater);
            LLVMHeuristicIntegerState.handleValues(vals, newWeakInverse, newStrictInverse, true, !greater);
            LLVMHeuristicIntegerState.handleValues(vals, newStrictInverse, newStrictInverse, false, !greater);
            YNM intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    weak,
                    newWeak,
                    false,
                    false,
                    greater,
                    secondLinear,
                    true,
                    false
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
            intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    newStrictInverse,
                    newWeakInverse,
                    true,
                    false,
                    !greater,
                    secondLinear,
                    false,
                    true
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
            intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    strictInverse,
                    newWeakInverse,
                    true,
                    false,
                    !greater,
                    secondLinear,
                    false,
                    true
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
            intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    strictInverse,
                    newStrictInverse,
                    false,
                    false,
                    !greater,
                    secondLinear,
                    false,
                    false
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
            intermediate =
                LLVMHeuristicIntegerState.updateWithOldKnowledge(
                    maxNumOfVarOccs,
                    highestFactor,
                    arrayPatterns,
                    weakInverse,
                    newWeakInverse,
                    false,
                    false,
                    !greater,
                    secondLinear,
                    false,
                    true
                );
            if (intermediate != YNM.MAYBE) {
                return intermediate;
            }
        }
        // the offset of secondExpr must limit the offset of the found expression in the other direction (the sets go
        // away from firstExpr towards secondExpr)
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = secondExpr.toLinear();
        if (linear.x != null) {
            // remember: we want to check firstExpr (greater ? >= : <=) secondExpr
            for (LLVMHeuristicTerm weakExpr : weak) {
                // remember: we have firstExpr (greater ? >= : <=) weakExpr
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> weakLinear = weakExpr.toLinear();
                if (
                    linear.x.equals(weakLinear.x)
                    && linear.z.compareTo(weakLinear.z) == 0
                    && LLVMHeuristicIntegerState.isInRelation(weakLinear.y, linear.y, false, greater)
                ) {
                    return YNM.YES;
                }
            }
            for (LLVMHeuristicTerm strictInvExpr : strictInverse) {
                // remember: we have firstExpr (greater ? < : >) strictInvExpr
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> strictInvLinear = strictInvExpr.toLinear();
                if (
                    linear.x.equals(strictInvLinear.x)
                    && linear.z.compareTo(strictInvLinear.z) == 0
                    && LLVMHeuristicIntegerState.isInRelation(strictInvLinear.y, linear.y, false, !greater)
                ) {
                    return YNM.NO;
                }
            }
            for (LLVMHeuristicTerm weakInvExpr : weakInverse) {
                // remember: we have firstExpr (greater ? <= : >=) weakInvExpr
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> weakInvLinear = weakInvExpr.toLinear();
                if (
                    linear.x.equals(weakInvLinear.x)
                    && linear.z.compareTo(weakInvLinear.z) == 0
                    && LLVMHeuristicIntegerState.isInRelation(weakInvLinear.y, linear.y, true, !greater)
                ) {
                    return YNM.NO;
                }
            }
        }
        // in case of a comparison with a constant, check if it is implied by a relation and the reference bounds
        if (secondExpr instanceof LLVMHeuristicConstRef) {
            LLVMHeuristicConstRef constant = (LLVMHeuristicConstRef) secondExpr;
            // remember: we want to check firstExpr (greater ? >= : <=) secondExpr
            for (LLVMHeuristicTerm weakExpr : weak) {
                // remember: we have firstExpr (greater ? >= : <=) weakExpr
                if (weakExpr.getNumberOfVarOccs() == 1 && weakExpr.isLinear()) {
                    LLVMHeuristicVariable ref = weakExpr.getVariables(false).iterator().next();
                    AbstractBoundedInt value = this.getValue(ref).getThisAsAbstractBoundedInt();
                    HashMap<LLVMHeuristicVariable, LLVMValue> map = new HashMap<LLVMHeuristicVariable, LLVMValue>();
                    map.put(ref, value);
                    try {
                        AbstractBoundedInt result = weakExpr.evaluate(map, this.params);
                        if (greater) {
                            BigInteger min = result.getLower().getConstant();
                            if (min.compareTo(constant.getIntegerValue()) >= 0) {
                                return YNM.YES;
                            }
                        } else {
                            BigInteger max = result.getUpper().getConstant();
                            if (max.compareTo(constant.getIntegerValue()) <= 0) {
                                return YNM.YES;
                            }
                        }
                    } catch (OverflowException e) {
                        continue;
                    }
                }
            }
            for (LLVMHeuristicTerm strictInvExpr : strictInverse) {
                // remember: we have firstExpr (greater ? < : >) strictInvExpr
                // for simplicity and efficiency, we only check expressions with one variable (may be adapted)
                if (strictInvExpr.getNumberOfVarOccs() == 1 && strictInvExpr.isLinear()) {
                    LLVMHeuristicVariable ref = strictInvExpr.getVariables(false).iterator().next();
                    AbstractBoundedInt value = this.getValue(ref).getThisAsAbstractBoundedInt();
                    HashMap<LLVMHeuristicVariable, LLVMValue> map = new HashMap<LLVMHeuristicVariable, LLVMValue>();
                    map.put(ref, value);
                    try {
                        AbstractBoundedInt result = strictInvExpr.evaluate(map, this.params);
                        if (greater) {
                            BigInteger max = result.getUpper().getConstant();
                            if (max.compareTo(constant.getIntegerValue()) <= 0) {
                                return YNM.NO;
                            }
                        } else {
                            BigInteger min = result.getLower().getConstant();
                            if (min.compareTo(constant.getIntegerValue()) >= 0) {
                                return YNM.NO;
                            }
                        }
                    } catch (OverflowException e) {
                        continue;
                    }
                }
            }
            for (LLVMHeuristicTerm weakInvExpr : weakInverse) {
                // remember: we have firstExpr (greater ? <= : >=) strictInvExpr
                // for simplicity and efficiency, we only check expressions with one variable (may be adapted)
                if (weakInvExpr.getNumberOfVarOccs() == 1 && weakInvExpr.isLinear()) {
                    LLVMHeuristicVariable ref = weakInvExpr.getVariables(false).iterator().next();
                    AbstractBoundedInt value = this.getValue(ref).getThisAsAbstractBoundedInt();
                    HashMap<LLVMHeuristicVariable, LLVMValue> map = new HashMap<LLVMHeuristicVariable, LLVMValue>();
                    map.put(ref, value);
                    try {
                        AbstractBoundedInt result = weakInvExpr.evaluate(map, this.params);
                        if (greater) {
                            BigInteger max = result.getUpper().getConstant();
                            if (max.compareTo(constant.getIntegerValue()) < 0) {
                                return YNM.NO;
                            }
                        } else {
                            BigInteger min = result.getLower().getConstant();
                            if (min.compareTo(constant.getIntegerValue()) > 0) {
                                return YNM.NO;
                            }
                        }
                    } catch (OverflowException e) {
                        continue;
                    }
                }
            }
        }
        // we cannot infer anything
        return YNM.MAYBE;
    }

    /**
     * Dumps an SMT problem consisting of the question whether the knowledge in a state and relation set implies a
     * certain relation to a new file in a folder specified in the DebuggingFlags.
     * @param dumper Dumper to send the query to.
     * @param state The state.
     * @param set The knowledge base (relation set).
     * @param rel The relation.
     */
    private void dumpSMTLIB(Z3ExtDumper dumper, LLVMHeuristicRelationSet set, LLVMHeuristicRelation rel) {
        dumper.addAssertion(
            Core.and(
                Core.and(
                    set.toSMTExp(),
                    LLVMHeuristicIntegerState.integerBoundInformationToSMTExp(this.getValues()),
                    Core.and(this.allocationInformationToSMTExp()),
                    this.associationInformationToSMTExp()
                ),
                Core.not(rel.toSMTExp())
            )
        );
        try {
            dumper.sendSAT();
        } catch (AbortionException | IOException | ParserException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /**
     * @param state The state holding the knowledge about the references.
     * @param knownRelations The known relations.
     * @param firstRef The first reference.
     * @param secondRef The second reference.
     * @param useCache Should we use the cache?
     * @return True if we can easily determine that the two references are unequal. False otherwise.
     */
    private boolean easyCheckForBeingUnequal(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicVariable firstRef,
        LLVMHeuristicVariable secondRef,
        boolean useCache
    ) {
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs = this.getAssociations();
        Integer firstAssociation = assocs.get(firstRef);
        Integer secondAssociation = assocs.get(secondRef);
        ImmutableSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> uneqCache = this.getUnequalCache();
        return
            (
                useCache
                && firstRef instanceof LLVMHeuristicVarRef
                && secondRef instanceof LLVMHeuristicVarRef
                && uneqCache.contains(
                    new ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>(
                        (LLVMHeuristicVarRef)firstRef,
                        (LLVMHeuristicVarRef)secondRef
                    )
                )
            ) || knownRelations.contains(relationFactory.notEqualTo(firstRef, secondRef))
            || knownRelations.contains(relationFactory.notEqualTo(secondRef, firstRef))
            || knownRelations.contains(relationFactory.lessThan(firstRef, secondRef))
            || knownRelations.contains(relationFactory.lessThan(secondRef, firstRef))
            || (firstAssociation != null && secondAssociation != null && !firstAssociation.equals(secondAssociation))
            || knownRelations.differentRemainderClasses(firstRef, secondRef);
    }

    /**
     * @param sets The old and new set to add expressions to.
     * @param inRelation An allocation (the order must be mirrored to the desired relation: old >= new means a <= b for
     *                   an allocation (a,b)).
     * @param assocsForAlloc The associated references to the considered allocation.
     * @param assocOffsets The association offsets.
     * @param useOffsets Use association offsets?
     */
    private void handleAllocation(
        Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>> sets,
        LLVMAllocation inRelation,
        Set<LLVMHeuristicVariable> assocsForAlloc,
        ImmutableMap<LLVMHeuristicVariable, BigInteger> assocOffsets,
        boolean useOffsets
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        for (LLVMHeuristicTerm expr : sets.x) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
            if (!inRelation.y.equals(exprLinear.x) || exprLinear.z.compareTo(BigInteger.ONE) != 0) {
                continue;
            }
            // inRelation.y >= inRelation.x implies
            // inRelation.y + exprOffset.y >= inRelation.x + exprOffset.y
            sets.y.add(
                termFactory.operation(
                    ArithmeticOperationType.ADD,
                    inRelation.x,
                    termFactory.constant(exprLinear.y)
                )
            );
            if (assocsForAlloc != null) {
                for (LLVMHeuristicVariable ref : assocsForAlloc) {
                    // inRelation.y >= ref + c implies inRelation.y + exprOffset.y >= ref + c + exprOffset.y
                    sets.y.add(
                        termFactory.create(
                            ArithmeticOperationType.ADD,
                            ref,
                            termFactory.constant(
                                useOffsets ? exprLinear.y.add(assocOffsets.get(ref)) : exprLinear.y
                            )
                        )
                    );
                }
            }
            break;
        }
    }

    /**
     * Adds expressions to the respective new sets which can be inferred from the old sets and allocation/association
     * information.
     * @param allocations The allocated memory areas.
     * @param assocs The associations.
     * @param assocOffsets The association offsets.
     * @param associationsInverse Mapping from allocated areas to sets of pointers being associated with them.
     * @param inDirection1 A pair of current/new sets of expressions in the specified direction.
     * @param inDirection2 Another pair of current/new sets of expressions in the specified direction.
     * @param againstDirection A pair of current/new sets of expressions against the specified direction.
     * @param directionIsGreater Is the specified direction the >= direction (i.e., elements x in the new set in
     *                           direction satisfy y >= x for some element y in the current set in direction)?
     */
    private void handleAllocationsAndAssociations(
        ImmutableList<LLVMAllocation> allocations,
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs,
        ImmutableMap<LLVMHeuristicVariable, BigInteger> assocOffsets,
        Map<LLVMAllocation, Set<LLVMHeuristicVariable>> associationsInverse,
        Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>> inDirection1,
        Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>> inDirection2,
        Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>> againstDirection,
        boolean directionIsGreater
    ) {
        if (directionIsGreater) {
            for (LLVMAllocation allocation : allocations) {
                Set<LLVMHeuristicVariable> assocsForAlloc = associationsInverse.get(allocation);
                this.handleAllocation(
                    inDirection1,
                    allocation,
                    assocsForAlloc,
                    assocOffsets,
                    true
                );
                this.handleAllocation(
                    inDirection2,
                    allocation,
                    assocsForAlloc,
                    assocOffsets,
                    true
                );
                this.handleAllocation(
                    againstDirection,
                    new LLVMAllocation(allocation.y, allocation.x),
                    assocsForAlloc,
                    assocOffsets,
                    false
                );
            }
        } else {
            for (LLVMAllocation allocation : allocations) {
                Set<LLVMHeuristicVariable> assocsForAlloc = associationsInverse.get(allocation);
                LLVMAllocation reversedAllocation = new LLVMAllocation(allocation.y, allocation.x);
                this.handleAllocation(
                    inDirection1,
                    reversedAllocation,
                    assocsForAlloc,
                    assocOffsets,
                    false
                );
                this.handleAllocation(
                    inDirection2,
                    reversedAllocation,
                    assocsForAlloc,
                    assocOffsets,
                    false
                );
                this.handleAllocation(
                    againstDirection,
                    allocation,
                    assocsForAlloc,
                    assocOffsets,
                    true
                );
            }
        }
        this.handleAssociations(
            allocations,
            assocs,
            assocOffsets,
            inDirection1,
            directionIsGreater
        );
        this.handleAssociations(
            allocations,
            assocs,
            assocOffsets,
            inDirection2,
            directionIsGreater
        );
        this.handleAssociations(
            allocations,
            assocs,
            assocOffsets,
            againstDirection,
            !directionIsGreater
        );
    }

    /**
     * @param allocations The list of allocations.
     * @param assocs The associations.
     * @param assocOffsets The association offsets.
     * @param sets The current/new set of expressions.
     * @param greater Greater relation?
     */
    private void handleAssociations(
        ImmutableList<LLVMAllocation> allocations,
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs,
        ImmutableMap<LLVMHeuristicVariable, BigInteger> assocOffsets,
        Pair<Set<LLVMHeuristicTerm>, Set<LLVMHeuristicTerm>> sets,
        boolean greater
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        for (LLVMHeuristicTerm expr : sets.x) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
            if (!assocs.containsKey(exprLinear.x)) {
                continue;
            }
            LLVMAllocation allocation = allocations.get(assocs.get(exprLinear.x));
            // allocation.x <= exprLinear.x <= exprLinear.x + associationOffsets.get(exprLinear.x) <= allocation.y
            BigInteger offset;
            final LLVMHeuristicVariable limit;
            if (
                (greater && exprLinear.z.compareTo(BigInteger.ZERO) > 0)
                || (!greater && exprLinear.z.compareTo(BigInteger.ZERO) < 0)
            ) {
                // exprLinear.z * exprLinear.x + exprLinear.y >=
                // exprLinear.z * allocation.x + exprLinear.y
                limit = (LLVMHeuristicVariable)allocation.x;
                offset = exprLinear.y;
            } else {
                // exprLinear.z * exprLinear.x + exprLinear.y <=
                // exprLinear.z * allocation.y - exprLinear.z * associationOffsets.get(exprLinear.x) + exprLinear.y
                limit = (LLVMHeuristicVariable)allocation.y;
                offset = exprLinear.y.subtract(assocOffsets.get(exprLinear.x).multiply(exprLinear.z));
            }
            sets.y.add(
                termFactory.create(
                    ArithmeticOperationType.ADD,
                    termFactory.create(ArithmeticOperationType.MUL, termFactory.constant(exprLinear.z), limit),
                    termFactory.constant(offset)
                )
            );
        }
    }

    /**
     * @param knownRelations The known relations.
     * @param firstExpr The first expression.
     * @param secondExpr The second expression.
     * @param strict Strict inequality?
     * @param greater Greater or less than?
     * @return YES if we can prove the specified relation between firstExpr and secondExpr, NO if we can prove the
     *         inverse relation, and MAYBE if we just do not know.
     */
    private YNM handleDirectedInequality(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicTerm secondExpr,
        boolean strict,
        boolean greater,
        Abortion aborter
    ) {
        final boolean isTautology;
        if (firstExpr instanceof LLVMHeuristicVariable && secondExpr instanceof LLVMHeuristicOperation) {
            isTautology =
                this.isTautologicalDirectedInequalityByValue(
                    (LLVMHeuristicVariable)firstExpr,
                    (LLVMHeuristicOperation)secondExpr,
                    strict,
                    !greater
                );
        } else if (firstExpr instanceof LLVMHeuristicOperation && secondExpr instanceof LLVMHeuristicVariable) {
            isTautology =
                this.isTautologicalDirectedInequalityByValue(
                    (LLVMHeuristicVariable)secondExpr,
                    (LLVMHeuristicOperation)firstExpr,
                    strict,
                    greater
                );
        } else {
            isTautology = false;
        }
        if (isTautology) {
            return YNM.YES;
        }
        // we can compute the transitive closure over our relations
        return
            strict ?
                this.checkForStrictInequalityInTransitiveClosure(
                    knownRelations,
                    firstExpr,
                    secondExpr,
                    greater,
                    aborter
                ) :
                    this.checkForWeakInequalityInTransitiveClosure(
                        knownRelations,
                        firstExpr,
                        secondExpr,
                        greater,
                        aborter
                    );
    }

    /**
     * @param state The abstract state holding the knowledge about the references.
     * @param ref A reference.
     * @param op An operation.
     * @param strict Strict inequality?
     * @param less Less or greater than?
     * @return True if ref is definitely in the specified relation to op (and we can find this out). False otherwise.
     */
    private boolean isTautologicalDirectedInequalityByValue(
        LLVMHeuristicVariable ref,
        LLVMHeuristicOperation op,
        boolean strict,
        boolean less
    ) {
        if (op != null & op.isSimple()) {
            LLVMHeuristicVariable opLhs = (LLVMHeuristicVariable)op.getLhs();
            LLVMHeuristicVariable opRhs = (LLVMHeuristicVariable)op.getRhs();
            LLVMHeuristicVariable otherRef;
            boolean isRight;
            if (opLhs.equals(ref)) {
                otherRef = opRhs;
                isRight = true;
            } else if (opRhs.equals(ref)) {
                otherRef = opLhs;
                isRight = false;
            } else {
                otherRef = null;
                isRight = false;
            }
            if (otherRef != null) {
                AbstractBoundedInt value = this.getValue(otherRef).getThisAsAbstractBoundedInt();
                switch (op.getOperation()) {
                    case ADD:
                        return LLVMHeuristicIntegerState.isInRelationByAddition(value, strict, less);
                    case SUB:
                        return isRight && LLVMHeuristicIntegerState.isInRelationBySubtraction(value, strict, less);
                    case MUL:
                        return LLVMHeuristicIntegerState.isInRelationByMultiplication(value, strict, less);
                    default:
                        // we do not know
                }
            }
        }
        return false;
    }

    /**
     * @param firstExpr The left-hand side.
     * @param secondExpr The right-hand side.
     * @return A pair of variables, if the given relation just consists of them. Null, if we do not know a way to do so.
     */
    private Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> toSimpleRelation(
        LLVMHeuristicTerm firstExpr,
        LLVMHeuristicTerm secondExpr
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        if (firstExpr instanceof LLVMHeuristicVariable && secondExpr instanceof LLVMHeuristicVariable) {
            return
                new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(
                    (LLVMHeuristicVariable)firstExpr,
                    (LLVMHeuristicVariable)secondExpr
                );
        } else if (firstExpr instanceof LLVMHeuristicOperation && secondExpr instanceof LLVMHeuristicConstRef) {
            final LLVMHeuristicConstRef rhsConst = (LLVMHeuristicConstRef)secondExpr;
            final LLVMHeuristicOperation lhsOp = (LLVMHeuristicOperation)firstExpr;
            final LLVMHeuristicTerm lhsOpLhs = lhsOp.getLhs();
            final LLVMHeuristicTerm lhsOpRhs = lhsOp.getRhs();
            if (
                lhsOp.getOperation() == ArithmeticOperationType.ADD
                && lhsOpLhs instanceof LLVMHeuristicConstRef
                && lhsOpRhs instanceof LLVMHeuristicVarRef
            ) {
                final LLVMHeuristicVariable variableRef = (LLVMHeuristicVariable)lhsOpRhs;
                final LLVMHeuristicVariable constRef =
                    termFactory.constant(
                        rhsConst.getIntegerValue().subtract(((LLVMHeuristicConstRef)lhsOpLhs).getIntegerValue())
                    );
                return new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(variableRef, constRef);
            }
        } else if (firstExpr instanceof LLVMHeuristicConstRef && secondExpr instanceof LLVMHeuristicOperation) {
            final LLVMHeuristicConstRef lhsConst = (LLVMHeuristicConstRef)firstExpr;
            final LLVMHeuristicOperation rhsOp = (LLVMHeuristicOperation)secondExpr;
            final LLVMHeuristicTerm rhsOpLhs = rhsOp.getLhs();
            final LLVMHeuristicTerm rhsOpRhs = rhsOp.getRhs();
            if (
                rhsOp.getOperation() == ArithmeticOperationType.ADD
                && rhsOpLhs instanceof LLVMHeuristicConstRef
                && rhsOpRhs instanceof LLVMHeuristicVarRef
            ) {
                final LLVMHeuristicVariable variableRef = (LLVMHeuristicVariable)rhsOpRhs;
                final LLVMHeuristicVariable constRef =
                    termFactory.constant(
                        lhsConst.getIntegerValue().subtract(((LLVMHeuristicConstRef)rhsOpLhs).getIntegerValue())
                    );
                return new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(constRef, variableRef);
            }
        }
        return null;
    }

    /**
     * @param state The abstract state holding the knowledge about the references.
     * @param knownRelations The known relations.
     * @param firstRef The first reference.
     * @param secondRef The second reference.
     * @param relType The relation type.
     * @param relTypeInverted The inverted relation type.
     * @param useCache Should we use the cache?
     * @return YES if we could prove the relation with easy checks, NO if we could prove its inverse, and MAYBE
     *         otherwise.
     */
    private YNM truthValueOfSimpleRelation(
        LLVMHeuristicRelationSet knownRelations,
        LLVMHeuristicVariable firstRef,
        LLVMHeuristicVariable secondRef,
        IntegerRelationType relType,
        IntegerRelationType relTypeInverted,
        boolean useCache
    ) {
        // First check if we know that the two references are unequal.
        // At the moment, this does not work: x < y implies x != y, so we might already have (x, y) in our uneqCache.
        // But if x < y is the relation to check, we always get 'true' here.
        // boolean areKnownToBeUnequal = this.easyCheckForBeingUnequal(knownRelations, firstRef, secondRef, useCache);
        boolean areKnownToBeUnequal = false;
        if (areKnownToBeUnequal) {
            switch (relType) {
            case EQ:
                return YNM.NO;
            case NE:
                return YNM.YES;
            default:
                // do nothing
            }
        }
        // Maybe the value has already been removed (this is the case if a call abstraction removed the respective
        // variables and the value has been replaced by a constant.)
        if (this.getValue(firstRef) == null || this.getValue(secondRef) == null) {
            return YNM.MAYBE;
        }
        // We cannot reason about floats yet.
        if (this.getValue(firstRef) instanceof AbstractFloat || this.getValue(secondRef) instanceof AbstractFloat) {
            return YNM.MAYBE;
        }
        // Check if we can find out the truth value by the values of the references.
        AbstractBoundedInt firstVal = this.getValue(firstRef).getThisAsAbstractBoundedInt();
        AbstractBoundedInt secondVal = this.getValue(secondRef).getThisAsAbstractBoundedInt();
        if (
            AbstractBoundedInt.computeComparisonResult(
                relType,
                firstVal,
                secondVal,
                false,
                areKnownToBeUnequal
            )
        ) {
            return YNM.YES;
        } else if (
            AbstractBoundedInt.computeComparisonResult(
                relTypeInverted,
                firstVal,
                secondVal,
                false,
                areKnownToBeUnequal
            )
        ) {
            return YNM.NO;
        }
        // check whether we have a weak inequality and know this by an allocation
        ImmutableList<LLVMAllocation> allocations = this.getAllocations();
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs = this.getAssociations();
        switch (relType) {
            case LE:
                if (allocations.contains(new LLVMAllocation(firstRef, secondRef))) {
                    return YNM.YES;
                }
                if (assocs.containsKey(firstRef)) {
                    if (allocations.get(assocs.get(firstRef)).y.equals(secondRef)) {
                        return YNM.YES;
                    }
                }
                if (assocs.containsKey(secondRef)) {
                    if (allocations.get(assocs.get(secondRef)).x.equals(firstRef)) {
                        return YNM.YES;
                    }
                }
                break;
            case LT:
                if (allocations.contains(new LLVMAllocation(secondRef, firstRef))) {
                    return YNM.NO;
                }
                if (assocs.containsKey(firstRef)) {
                    if (allocations.get(assocs.get(firstRef)).x.equals(secondRef)) {
                        return YNM.NO;
                    }
                }
                if (assocs.containsKey(secondRef)) {
                    if (allocations.get(assocs.get(secondRef)).y.equals(firstRef)) {
                        return YNM.NO;
                    }
                }
                break;
            case GE:
                if (allocations.contains(new LLVMAllocation(secondRef, firstRef))) {
                    return YNM.YES;
                }
                if (assocs.containsKey(firstRef)) {
                    if (allocations.get(assocs.get(firstRef)).x.equals(secondRef)) {
                        return YNM.YES;
                    }
                }
                if (assocs.containsKey(secondRef)) {
                    if (allocations.get(assocs.get(secondRef)).y.equals(firstRef)) {
                        return YNM.YES;
                    }
                }
                break;
            case GT:
                if (allocations.contains(new LLVMAllocation(firstRef, secondRef))) {
                    return YNM.NO;
                }
                if (assocs.containsKey(firstRef)) {
                    if (allocations.get(assocs.get(firstRef)).y.equals(secondRef)) {
                        return YNM.NO;
                    }
                }
                if (assocs.containsKey(secondRef)) {
                    if (allocations.get(assocs.get(secondRef)).x.equals(firstRef)) {
                        return YNM.NO;
                    }
                }
                break;
            case NE:
                if (assocs.containsKey(firstRef) && assocs.containsKey(secondRef)) {
                    if (!allocations.get(assocs.get(firstRef)).equals(allocations.get(assocs.get(secondRef)))) {
                        return YNM.YES;
                    }
                }
                break;
            default:
                // do nothing
        }
        return YNM.MAYBE;
    }

}

///**
//* @param baseState The base state.
//* @param firstRef The first reference.
//* @param relType The relation type of the relation to add.
//* @param secondRef The second reference.
//* @param params Strategy parameters.
//* @return A set of two pairs of states and corresponding state change information which emerge from the baseState
//*         by adding the specified relation firstRef relType secondRef and its inverse.
//*/
//public static Set<RefinementResult> addRelationAndInverse(
// LLVMAbstractState baseState,
// LLVMHeuristicVariable firstRef,
// IntegerRelationType relType,
// LLVMHeuristicVariable secondRef,
// LLVMParameters params
//) {
// Set<RefinementResult> out = new LinkedHashSet<RefinementResult>();
// // Just create two successors, one where it holds and one where it does not:
// LLVMAbstractState trueState;
// LLVMAbstractState falseState;
// Collection<LLVMHeuristicRelation> trueStateChangeInformation = new LinkedHashSet<LLVMHeuristicRelation>();
// Collection<LLVMHeuristicRelation> falseStateChangeInformation = new LinkedHashSet<LLVMHeuristicRelation>();
// Map<LLVMHeuristicVariable, LLVMHeuristicVariable> trueReplacements = new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
// Map<LLVMHeuristicVariable, LLVMHeuristicVariable> falseReplacements = new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
// Pair<LLVMAbstractState, LLVMAbstractState> pair;
// // In case of an equality check in the relation, we can do a special trick and just identify references:
// switch (relType) {
//     case EQ:
//         pair =
//             LLVMHeuristicIntegerState.addEquationAndInverse(
//                 baseState,
//                 firstRef,
//                 secondRef,
//                 trueReplacements,
//                 falseReplacements,
//                 trueStateChangeInformation,
//                 falseStateChangeInformation,
//                 params
//             );
//         trueState = pair.x;
//         falseState = pair.y;
//         break;
//     case NE:
//         pair =
//             LLVMHeuristicIntegerState.addEquationAndInverse(
//                 baseState,
//                 firstRef,
//                 secondRef,
//                 falseReplacements,
//                 trueReplacements,
//                 falseStateChangeInformation,
//                 trueStateChangeInformation,
//                 params
//             );
//         // note the swap
//         trueState = pair.y;
//         falseState = pair.x;
//         break;
//     case LE:
//         pair =
//             LLVMHeuristicIntegerState.addLEAndInverse(
//                 baseState,
//                 firstRef,
//                 secondRef,
//                 trueReplacements,
//                 falseReplacements,
//                 trueStateChangeInformation,
//                 falseStateChangeInformation,
//                 params
//             );
//         trueState = pair.x;
//         falseState = pair.y;
//         break;
//     case LT:
//         pair =
//             LLVMHeuristicIntegerState.addLTAndInverse(
//                 baseState,
//                 firstRef,
//                 secondRef,
//                 trueReplacements,
//                 falseReplacements,
//                 trueStateChangeInformation,
//                 falseStateChangeInformation,
//                 params
//             );
//         trueState = pair.x;
//         falseState = pair.y;
//         break;
//     case GE:
//         pair =
//             LLVMHeuristicIntegerState.addLEAndInverse(
//                 baseState,
//                 secondRef,
//                 firstRef,
//                 trueReplacements,
//                 falseReplacements,
//                 trueStateChangeInformation,
//                 falseStateChangeInformation,
//                 params
//             );
//         trueState = pair.x;
//         falseState = pair.y;
//         break;
//     case GT:
//         pair =
//             LLVMHeuristicIntegerState.addLTAndInverse(
//                 baseState,
//                 secondRef,
//                 firstRef,
//                 trueReplacements,
//                 falseReplacements,
//                 trueStateChangeInformation,
//                 falseStateChangeInformation,
//                 params
//             );
//         trueState = pair.x;
//         falseState = pair.y;
//         break;
//     default:
//         throw new IllegalStateException("Someone found a new way to create relations...");
// }
// out.add(
//     LLVMHeuristicIntegerState.computeRefinementResult(
//         trueState,
//         trueStateChangeInformation,
//         trueReplacements,
//         params
//     )
// );
// out.add(
//     LLVMHeuristicIntegerState.computeRefinementResult(
//         falseState,
//         falseStateChangeInformation,
//         falseReplacements,
//         params
//     )
// );
// return out;
//}

///**
//* @param baseState The base state.
//* @param operation The left hand side operation.
//* @param relType The relation type of the relation to add.
//* @param bound The bound for the left hand side.
//* @param params Strategy parameters.
//* @return A set of two pairs of states and corresponding state change information which emerge from the baseState
//*         by adding the specified relation firstRef relType secondRef and its inverse.
//*/
//public static Set<RefinementResult> addRelationAndInverse(
// LLVMAbstractState baseState,
// LLVMHeuristicOperation operation,
// IntegerRelationType relType,
// LLVMHeuristicConstRef bound,
// LLVMParameters params
//) {
// Set<RefinementResult> out = new LinkedHashSet<RefinementResult>();
// // Just create two successors, one where it holds and one where it does not:
// LLVMAbstractState trueState;
// LLVMAbstractState falseState;
// Collection<LLVMHeuristicRelation> trueStateChangeInformation = new LinkedHashSet<LLVMHeuristicRelation>();
// Collection<LLVMHeuristicRelation> falseStateChangeInformation = new LinkedHashSet<LLVMHeuristicRelation>();
// Map<LLVMHeuristicVariable, LLVMHeuristicVariable> trueReplacements = new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
// Map<LLVMHeuristicVariable, LLVMHeuristicVariable> falseReplacements = new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
// Pair<LLVMAbstractState, LLVMAbstractState> pair;
// // In case of an equality check in the relation, we can do a special trick and just identify references:
// switch (relType) {
//     case EQ:
//     case NE:
//         throw new IllegalArgumentException("Bound relations should be inequalities of type 'LE' or 'GE'.");
//     case GT:
//     case LE:
//         pair =
//             LLVMHeuristicIntegerState.addLEAndInverse(
//                 baseState,
//                 operation,
//                 bound,
//                 trueReplacements,
//                 falseReplacements,
//                 trueStateChangeInformation,
//                 falseStateChangeInformation,
//                 params
//             );
//         trueState = pair.x;
//         falseState = pair.y;
//         break;
//     case LT:
//     case GE:
//         pair =
//             LLVMHeuristicIntegerState.addLEAndInverse(
//                 baseState,
//                 bound,
//                 operation,
//                 trueReplacements,
//                 falseReplacements,
//                 trueStateChangeInformation,
//                 falseStateChangeInformation,
//                 params
//             );
//         trueState = pair.x;
//         falseState = pair.y;
//         break;
//     default:
//         throw new IllegalStateException("Someone found a new way to create relations...");
// }
// out.add(
//     LLVMHeuristicIntegerState.computeRefinementResult(
//         trueState,
//         trueStateChangeInformation,
//         trueReplacements,
//         params
//     )
// );
// out.add(
//     LLVMHeuristicIntegerState.computeRefinementResult(
//         falseState,
//         falseStateChangeInformation,
//         falseReplacements,
//         params
//     )
// );
// return out;
//}

///**
// * @param state Some state.
// * @param litOfInterest Some literal in <code>state</code> for which we need to have a definite boolean value.
// * @param params Strategy parameters.
// * @return A set which will be filled by two states and corresponding state change information if refinement was
// *         needed. Null otherwise.
// */
//public static Set<RefinementResult> refineBooleanValue(
//    LLVMAbstractState state,
//    BasicLiteral litOfInterest,
//    LLVMParameters params
//) {
//    // Get the current value of the literal of interest to find out if we need to refine:
//    LLVMHeuristicVariable varRef = state.getTermForLiteral(litOfInterest);
//    LLVMValue curValue = state.getValue(varRef);
//    if (curValue instanceof LLVMTrapValue) {
//        // as boolean values can only be refined to concrete values, there is nothing to refine for a trap value
//        return null;
//    }
//    AbstractBoundedInt curVal = curValue.getThisAsAbstractBoundedInt();
//    // For a concrete value, we do not need to refine:
//    if (curVal.isLiteral()) {
//        return null;
//    }
//    // Create one successor for the "true" case and one for the "false" case:
//    if (Globals.useAssertions) {
//        assert (litOfInterest instanceof BasicVariableName) : "Abstract value for non-variable";
//    }
//    String varName = ((BasicVariableName)litOfInterest).getName();
//    // TODO check whether the true/false interpretation of 0 and 1 is right
//    Set<RefinementResult> out = new LinkedHashSet<RefinementResult>();
//    Set<LLVMHeuristicVariable> oldUsedRefs = state.getUsedReferences(true);
//    out.add(
//        new RefinementResult(
//            state.setProgramVariable(
//                varName,
//                LLVMHeuristicTermFactory.ZERO,
//                BasicIntType.I1
//            ).restrictToUsedReferences(oldUsedRefs, params).setRefined(true),
//            Collections.<LLVMStateChangeInformation>emptySet(),
//            Collections.<LLVMHeuristicVariable, LLVMHeuristicVariable>emptyMap()
//        )
//    );
//    out.add(
//        new RefinementResult(
//            state.setProgramVariable(
//                varName,
//                LLVMHeuristicTermFactory.ONE,
//                BasicIntType.I1
//            ).restrictToUsedReferences(oldUsedRefs, params).setRefined(true),
//            Collections.<LLVMStateChangeInformation>emptySet(),
//            Collections.<LLVMHeuristicVariable, LLVMHeuristicVariable>emptyMap()
//        )
//    );
//    return out;
//}

///**
// * Checks if a given relation can be decided in some state. If this is the case, <code>false</code> is returned and
// * nothing happens to <code>out</code>. Otherwise, a number of successors in which the relation should be decidable
// * are created, added to <code>out</code> and <code>true</code> is returned. This is either achieved by
// * partitioning the integer variables in a useful way or by simply creating successors for both cases, adding the
// * relation (or its inverse) to the respective relation set.
// * @param baseState The state that will be refined, if needed.
// * @param firstRef The first reference.
// * @param relType The relation between the two references, i.e., we consider
// *                <code>firstRef</code> <code>relType</code> <code>secondRef</code>.
// * @param secondRef The second reference.
// * @param params Strategy parameters.
// * @return The set that will hold results of our computation or null if no refinement was needed.
// */
//public static Set<RefinementResult> refineIntegerValuesForRelation(
//    LLVMAbstractState baseState,
//    LLVMHeuristicVariable firstRef,
//    IntegerRelationType relType,
//    LLVMHeuristicVariable secondRef,
//    LLVMParameters params
//) {
//    // Check if this is already known:
//    if (
//        this.truthValueOfRelation(
//            baseState,
//            firstRef,
//            relType,
//            secondRef,
//            true,
//            params
//        ) != YNM.MAYBE
//    ) {
//        return null;
//    }
//    LLVMValue firstValue = baseState.getValue(firstRef);
//    LLVMValue secondValue = baseState.getValue(secondRef);
//    AbstractInt firstVal = firstValue.getThisAsAbstractInt();
//    AbstractInt secondVal = secondValue.getThisAsAbstractInt();
//    // OK, we need to do things. Try refining the values:
//    Collection<Pair<AbstractInt, AbstractInt>> refinedIntegers =
//        IntegerRefinement.forIntegerRelation(firstVal, secondVal, relType);
//    if (refinedIntegers == null) {
//        return LLVMHeuristicIntegerState.addRelationAndInverse(baseState, firstRef, relType, secondRef, params);
//    } else {
//        // We could refine the values, yay:
//        Set<RefinementResult> out = new LinkedHashSet<RefinementResult>();
//        for (Pair<AbstractInt, AbstractInt> refinedPair : refinedIntegers) {
//            AbstractBoundedInt first = refinedPair.x.getThisAsAbstractBoundedInt();
//            AbstractBoundedInt second = refinedPair.y.getThisAsAbstractBoundedInt();
//            params.aborter.checkAbortion();
//            LLVMAbstractState newState = baseState;
//            LLVMHeuristicRelationSet changeInfo = new LLVMHeuristicRelationSet();
//            if (first.isIntLiteral()) {
//                if (firstValue instanceof LLVMTrapValue) {
//                    // this refinement does not work
//                    return null;
//                }
//                LLVMHeuristicVariable firstConst = first.createLLVMRef();
//                newState = newState.replaceSymbolicVariable(firstRef, firstConst);
//                if (!firstRef.isConcrete()) {
//                    changeInfo.add(
//                        new LLVMHeuristicRelation(
//                            LLVMHeuristicRelationType.EQ,
//                            firstRef,
//                            firstConst
//                        )
//                    );
//                }
//            } else {
//                LLVMValue nextVal = first;
//                if (firstValue instanceof LLVMTrapValue) {
//                    nextVal = new LLVMTrapValue(nextVal, ((LLVMTrapValue)firstValue).getAssociationDependency());
//                }
//                newState = newState.setValue(firstRef, nextVal);
//                IntervalBound lower = first.getLower();
//                IntervalBound upper = first.getUpper();
//                if (lower.isFinite()) {
//                    changeInfo.add(
//                        new LLVMHeuristicRelation(
//                            LLVMHeuristicRelationType.LE,
//                            new LLVMHeuristicConstRef(lower.getConstant()),
//                            firstRef
//                        )
//                    );
//                }
//                if (upper.isFinite()) {
//                    changeInfo.add(
//                        new LLVMHeuristicRelation(
//                            LLVMHeuristicRelationType.LE,
//                            firstRef,
//                            new LLVMHeuristicConstRef(upper.getConstant())
//                        )
//                    );
//                }
//            }
//            if (second.isIntLiteral()) {
//                if (secondValue instanceof LLVMTrapValue) {
//                    // this refinement does not work
//                    return null;
//                }
//                LLVMHeuristicVariable secondConst = second.createLLVMRef();
//                newState = newState.replaceSymbolicVariable(secondRef, secondConst);
//                if (!secondRef.isConcrete()) {
//                    changeInfo.add(
//                        new LLVMHeuristicRelation(
//                            LLVMHeuristicRelationType.EQ,
//                            secondRef,
//                            secondConst
//                        )
//                    );
//                }
//            } else {
//                LLVMValue nextVal = second;
//                if (secondValue instanceof LLVMTrapValue) {
//                    nextVal = new LLVMTrapValue(nextVal, ((LLVMTrapValue)secondValue).getAssociationDependency());
//                }
//                newState = newState.setValue(secondRef, nextVal);
//                IntervalBound lower = second.getLower();
//                IntervalBound upper = second.getUpper();
//                if (lower.isFinite()) {
//                    changeInfo.add(
//                        new LLVMHeuristicRelation(
//                            LLVMHeuristicRelationType.LE,
//                            new LLVMHeuristicConstRef(lower.getConstant()),
//                            secondRef
//                        )
//                    );
//                }
//                if (upper.isFinite()) {
//                    changeInfo.add(
//                        new LLVMHeuristicRelation(
//                            LLVMHeuristicRelationType.LE,
//                            secondRef,
//                            new LLVMHeuristicConstRef(upper.getConstant())
//                        )
//                    );
//                }
//            }
//            KnowledgeResult adjusted = newState.adjustValues(params);
//            changeInfo.replaceReferences(adjusted.z);
//            for (Map.Entry<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> entry : adjusted.y.entrySet()) {
//                LLVMHeuristicVariable key = entry.getKey();
//                Pair<BigInteger, BigInteger> value = entry.getValue();
//                if (value.x != null) {
//                    if (value.y != null) {
//                        if (Globals.useAssertions) {
//                            assert (value.x.compareTo(value.y) < 0) : "Inconsistent value update!";
//                        }
//                        changeInfo.add(
//                            new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, key, new LLVMHeuristicConstRef(value.y))
//                        );
//                        changeInfo.add(
//                            new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, new LLVMHeuristicConstRef(value.x), key)
//                        );
//                    } else {
//                        changeInfo.add(
//                            new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, new LLVMHeuristicConstRef(value.x), key)
//                        );
//                    }
//                } else if (value.y != null) {
//                    changeInfo.add(new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, key, new LLVMHeuristicConstRef(value.y)));
//                }
//            }
//            Iterator<Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable>> it = adjusted.z.entrySet().iterator();
//            while (it.hasNext()) {
//                Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> entry = it.next();
//                if (entry.getKey() instanceof LLVMHeuristicConstRef) {
//                    it.remove();
//                }
//            }
//LLVMAbstractState resState = adjusted.x;
//resState = resState.findFurtherAssociations(changeInfo, params);
//resState = resState.findFurtherInvariants(changeInfo, params);
//out.add(
//    new RefinementResult(
//        resState.setRefined(true),
//        changeInfo,
//        adjusted.z
//    )
//);
//        }
//        if (Globals.useAssertions && DebuggingFlags.CHECK_INVARIANTS) {
//            assert (out.size() > 1) : "Refinement did not lead to more than one successor!";
//        }
//        return out;
//    }
//}
//
///**
// * Checks if a given relation can be decided in some state. If this is the case, <code>false</code> is returned and
// * nothing happens to <code>out</code>. Otherwise, a number of successors in which the relation should be decidable
// * are created, added to <code>out</code> and <code>true</code> is returned. This is either achieved by creating
// * successors for both cases, adding the relation (or its inverse) to the respective relation set.
// * @param baseState The state that will be refined, if needed.
// * @param operation The operation to be checked against a bound.
// * @param relType The relation between the two references, i.e., we consider
// *                <code>firstRef</code> <code>relType</code> <code>secondRef</code>.
// * @param bound The bound.
// * @param params Strategy parameters.
// * @return The set that will hold results of our computation or null if no refinement was needed.
// */
//public static Set<RefinementResult> refineStateForBoundRelation(
//    LLVMAbstractState baseState,
//    LLVMHeuristicOperation operation,
//    IntegerRelationType relType,
//    LLVMHeuristicConstRef bound,
//    LLVMParameters params
//) {
//    // Check if this is already known:
//    if (
//        this.truthValueOfRelation(
//            baseState,
//            operation,
//            relType,
//            bound,
//            true,
//            params
//        ) != YNM.MAYBE
//    ) {
//        return null;
//    }
//    // OK, we need to do things.
//    return LLVMHeuristicIntegerState.addRelationAndInverse(baseState, operation, relType, bound, params);
//}

///**
// * If we have unit (i.e. containing only one variable) equations or know that some references must be equal, we can
// * replace the corresponding references by constants or just one of the equal references. Moreover, we also clean
// * the relations by dropping tautological or already implied relations.
// * @param state Some state.
// * @param params Strategy parameters.
// * @return A pair of 1) a state with replaced references and dropped unit equations and 2) the replacement map.
// */
//public static ReplacementResult resolveReferenceEqualities(
//    LLVMAbstractState state,
//    LLVMParameters params
//) {
//    // first replace variables by constants using unit equations
//    ReplacementResult res =
//        LLVMHeuristicIntegerState.replaceReferencesByConstantsUsingUnitEquations(state, params.aborter);
//    // collect all replacements in here
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements = res.y;
//    // now unify references known to be equal
//    res = LLVMHeuristicIntegerState.unifyEqualReferences(res.x, params);
//    LLVMHeuristicExpressionUtils.updateReplacements(replacements, res.y);
//    // finally, clean the relations
//    return new ReplacementResult(res.x.cleanRelations(params), replacements);
//}

///**
// * @param state The integer state holding the knowledge about the references.
// * @param knownRelations The known relations.
// * @param firstExpr The first expression.
// * @param relType The relation type.
// * @param secondExpr The second expression.
// * @param useCache Should we use the cache?
// * @param params Strategy parameters.
// * @return YES if the relation firstExpr relType secondExpr holds, NO if its inverse holds, and MAYBE if we just do
// *         not know.
// */
//public YNM truthValueOfRelation(
//    LLVMHeuristicRelationSet knownRelations,
//    LLVMHeuristicTerm firstExpr,
//    LLVMHeuristicRelationType relType,
//    LLVMHeuristicTerm secondExpr,
//    boolean useCache
//) {
//    final LLVMHeuristicRelation relationToCheck;
//    if (relType.equals(IntegerRelationType.GT) || relType.equals(IntegerRelationType.GE)) {
//        relationToCheck =
//            new LLVMHeuristicRelation(LLVMHeuristicRelationType.fromIntegerRelationType(relType.mirror()), secondExpr, firstExpr);
//    } else {
//        relationToCheck = new LLVMHeuristicRelation(LLVMHeuristicRelationType.fromIntegerRelationType(relType), firstExpr, secondExpr);
//    }
//
//    final IntegerState relationInterface = this.state.getIntegerState().addRelationSet(knownRelations);
//    final IntegerState useCacheInterface =
//        setUseCacheOnLLVMIntegerState(relationInterface, useCache);
//    return useCacheInterface.checkRelation(relationToCheck);
//}

///**
// * @param baseState The base state.
// * @param firstRef The first reference.
// * @param secondRef The second reference.
// * @param trueReplacements The replacements performed for the true state.
// * @param falseReplacements The replacements performed for the false state.
// * @param trueStateChangeInformation The relations added to the true state.
// * @param falseStateChangeInformation The relations added to the false state.
// * @param params Strategy parameters.
// * @return Two states emerging from the base state by unifying the references and adding an inequality.
// */
//private static Pair<LLVMAbstractState, LLVMAbstractState> addEquationAndInverse(
//    LLVMAbstractState baseState,
//    LLVMHeuristicVariable firstRef,
//    LLVMHeuristicVariable secondRef,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> trueReplacements,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> falseReplacements,
//    Collection<LLVMHeuristicRelation> trueStateChangeInformation,
//    Collection<LLVMHeuristicRelation> falseStateChangeInformation,
//    LLVMParameters params
//) {
//    // In the true case, we just replace one variable by the other:
//    ReplacementResult unificationResult = baseState.unifySymbolicVariables(firstRef, secondRef, params);
//    for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> entry : unificationResult.y.entrySet()) {
//        if (!entry.getKey().isConcrete()) {
//            trueReplacements.put(entry.getKey(), entry.getValue());
//        }
//    }
//    Set<LLVMHeuristicRelation> store = new LinkedHashSet<LLVMHeuristicRelation>(trueStateChangeInformation);
//    for (LLVMHeuristicRelation rel : store) {
//        trueStateChangeInformation.add(rel.applySubstitution(unificationResult.y));
//    }
//    Pair<LLVMAbstractState, LLVMHeuristicRelationSet> addingResult =
//        baseState.addRelations(
//            LLVMHeuristicIntegerState.getStrongestRelations(
//                baseState,
//                new LLVMHeuristicRelation(LLVMHeuristicRelationType.NE, firstRef, secondRef),
//                params
//            ),
//            params
//        );
//    falseStateChangeInformation.addAll(addingResult.y);
//    return new Pair<LLVMAbstractState, LLVMAbstractState>(
//        unificationResult.x.cleanRelations(params),
//        addingResult.x
//    );
//}

///**
// * Refine the current state for a bound relation, e.g. MinInt <= x + y, where x and y are non-concrete references.
// * @param baseState The base state.
// * @param bound The left hand side.
// * @param operation The right hand side.
// * @param trueReplacements The replacements for the true state.
// * @param falseReplacements The replacements for the false state.
// * @param trueStateChangeInformation The relations added to the true state.
// * @param falseStateChangeInformation The relations added to the false state.
// * @param params Strategy parameters.
// * @return Two states emerging from the base state by adding an LE relation between the references and an inverse
// *         relation.
// */
//private static Pair<LLVMAbstractState, LLVMAbstractState> addLEAndInverse(
//    LLVMAbstractState baseState,
//    LLVMHeuristicConstRef bound,
//    LLVMHeuristicOperation operation,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> trueReplacements,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> falseReplacements,
//    Collection<LLVMHeuristicRelation> trueStateChangeInformation,
//    Collection<LLVMHeuristicRelation> falseStateChangeInformation,
//    LLVMParameters params
//) {
//    if (Globals.useAssertions && DebuggingFlags.CHECK_INVARIANTS) {
//        assert (
//            !(operation.getLhs() instanceof LLVMHeuristicConstRef)
//            && !(operation.getRhs() instanceof LLVMHeuristicConstRef)
//        ) : "A relation on constants should be decidable!";
//    }
//    LLVMAbstractState trueState;
//    Pair<LLVMAbstractState, LLVMHeuristicRelationSet> addingResult =
//        baseState.addRelations(
//            LLVMHeuristicIntegerState.getStrongestRelations(
//                baseState,
//                new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, bound, operation),
//                params
//            ),
//            params
//        );
//    trueState = addingResult.x;
//    trueStateChangeInformation.addAll(addingResult.y);
//    addingResult =
//        baseState.addRelations(
//            LLVMHeuristicIntegerState.getStrongestRelations(
//                baseState,
//                new LLVMHeuristicRelation(LLVMHeuristicRelationType.LT, operation, bound),
//                params
//            ),
//            params
//        );
//    falseStateChangeInformation.addAll(addingResult.y);
//    return new Pair<LLVMAbstractState, LLVMAbstractState>(trueState, addingResult.x);
//}

///**
// * @param baseState The base state.
// * @param firstRef The first reference.
// * @param secondRef The second reference.
// * @param trueReplacements The replacements for the true state.
// * @param falseReplacements The replacements for the false state.
// * @param trueStateChangeInformation The relations added to the true state.
// * @param falseStateChangeInformation The relations added to the false state.
// * @param params Strategy parameters.
// * @return Two states emerging from the base state by adding an LE relation between the references and an inverse
// *         relation.
// */
//private static Pair<LLVMAbstractState, LLVMAbstractState> addLEAndInverse(
//    LLVMAbstractState baseState,
//    LLVMHeuristicVariable firstRef,
//    LLVMHeuristicVariable secondRef,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> trueReplacements,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> falseReplacements,
//    Collection<LLVMHeuristicRelation> trueStateChangeInformation,
//    Collection<LLVMHeuristicRelation> falseStateChangeInformation,
//    LLVMParameters params
//) {
//    LLVMAbstractState trueState;
//    // if we also have secondRef <= firstRef, we have an equation in the true state
//    if (
//        this.truthValueOfRelation(
//            baseState,
//            secondRef,
//            IntegerRelationType.LE,
//            firstRef,
//            true,
//            params
//        ) == YNM.YES
//    ) {
//        Pair<LLVMAbstractState, Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> unificationResult =
//            baseState.unifySymbolicVariables(firstRef, secondRef, params);
//        trueState = unificationResult.x.cleanRelations(params);
//        for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> entry : unificationResult.y.entrySet()) {
//            if (!entry.getKey().isConcrete()) {
//                trueReplacements.put(entry.getKey(), entry.getValue());
//            }
//        }
//        Set<LLVMHeuristicRelation> store = new LinkedHashSet<LLVMHeuristicRelation>(trueStateChangeInformation);
//        trueStateChangeInformation.clear();
//        for (LLVMHeuristicRelation rel : store) {
//            trueStateChangeInformation.add(rel.applySubstitution(unificationResult.y));
//        }
//    } else {
//        Pair<LLVMAbstractState, LLVMHeuristicRelationSet> addingResult =
//            baseState.addRelations(
//                LLVMHeuristicIntegerState.getStrongestRelations(
//                    baseState,
//                    new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, firstRef, secondRef),
//                    params
//                ),
//                params
//            );
//        trueState = addingResult.x;
//        trueStateChangeInformation.addAll(addingResult.y);
//    }
//    Pair<LLVMAbstractState, LLVMHeuristicRelationSet> addingResult =
//        baseState.addRelations(
//            LLVMHeuristicIntegerState.getStrongestRelations(
//                baseState,
//                new LLVMHeuristicRelation(LLVMHeuristicRelationType.LT, secondRef, firstRef),
//                params
//            ),
//            params
//        );
//    falseStateChangeInformation.addAll(addingResult.y);
//    return new Pair<LLVMAbstractState, LLVMAbstractState>(trueState, addingResult.x);
//}

///**
// * Refine the current state for a bound relation, e.g. x + y <= MaxInt, where x and y are non-concrete references.
// * @param baseState The base state.
// * @param operation The left hand side.
// * @param bound The right hand side.
// * @param trueReplacements The replacements for the true state.
// * @param falseReplacements The replacements for the false state.
// * @param trueStateChangeInformation The relations added to the true state.
// * @param falseStateChangeInformation The relations added to the false state.
// * @param params Strategy parameters.
// * @return Two states emerging from the base state by adding an LE relation between the references and an inverse
// *         relation.
// */
//private static Pair<LLVMAbstractState, LLVMAbstractState> addLEAndInverse(
//    LLVMAbstractState baseState,
//    LLVMHeuristicOperation operation,
//    LLVMHeuristicConstRef bound,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> trueReplacements,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> falseReplacements,
//    Collection<LLVMHeuristicRelation> trueStateChangeInformation,
//    Collection<LLVMHeuristicRelation> falseStateChangeInformation,
//    LLVMParameters params
//) {
//    if (Globals.useAssertions && DebuggingFlags.CHECK_INVARIANTS) {
//        assert (
//            !(operation.getLhs() instanceof LLVMHeuristicConstRef)
//            && !(operation.getRhs() instanceof LLVMHeuristicConstRef)
//        ) : "A relation on constants should be decidable!";
//    }
//    LLVMAbstractState trueState;
//    Pair<LLVMAbstractState, LLVMHeuristicRelationSet> addingResult =
//        baseState.addRelations(
//            LLVMHeuristicIntegerState.getStrongestRelations(
//                baseState,
//                new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, operation, bound),
//                params
//            ),
//            params
//        );
//    trueState = addingResult.x;
//    trueStateChangeInformation.addAll(addingResult.y);
//    addingResult =
//        baseState.addRelations(
//            LLVMHeuristicIntegerState.getStrongestRelations(
//                baseState,
//                new LLVMHeuristicRelation(LLVMHeuristicRelationType.LT, bound, operation),
//                params
//            ),
//            params
//        );
//    falseStateChangeInformation.addAll(addingResult.y);
//    return new Pair<LLVMAbstractState, LLVMAbstractState>(trueState, addingResult.x);
//}

///**
// * @param baseState The base state.
// * @param firstRef The first reference.
// * @param secondRef The second reference.
// * @param trueReplacements The replacements for the true state.
// * @param falseReplacements The replacements for the false state.
// * @param trueStateChangeInformation The relations added to the true state.
// * @param falseStateChangeInformation The relations added to the false state.
// * @param params Strategy parameters.
// * @return Two states emerging from the base state by adding a LT relation between the references and an inverse
// *         relation.
// */
//private static Pair<LLVMAbstractState, LLVMAbstractState> addLTAndInverse(
//    LLVMAbstractState baseState,
//    LLVMHeuristicVariable firstRef,
//    LLVMHeuristicVariable secondRef,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> trueReplacements,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> falseReplacements,
//    Collection<LLVMHeuristicRelation> trueStateChangeInformation,
//    Collection<LLVMHeuristicRelation> falseStateChangeInformation,
//    LLVMParameters params
//) {
//    Pair<LLVMAbstractState, LLVMHeuristicRelationSet> addingResult =
//        baseState.addRelations(
//            LLVMHeuristicIntegerState.getStrongestRelations(
//                baseState,
//                new LLVMHeuristicRelation(LLVMHeuristicRelationType.LT, firstRef, secondRef),
//                params
//            ),
//            params
//        );
//    LLVMAbstractState trueState = addingResult.x;
//    trueStateChangeInformation.addAll(addingResult.y);
//    LLVMAbstractState falseState;
//    // if we also have firstRef <= secondRef, we have an equation in the false state
//    if (
//        this.truthValueOfRelation(
//            baseState,
//            firstRef,
//            IntegerRelationType.LE,
//            secondRef,
//            true,
//            params
//        ) == YNM.YES
//    ) {
//        Pair<LLVMAbstractState, Map<LLVMHeuristicVariable, LLVMHeuristicVariable>> unificationResult =
//            baseState.unifySymbolicVariables(firstRef, secondRef, params);
//        falseState = unificationResult.x.cleanRelations(params);
//        for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> entry : unificationResult.y.entrySet()) {
//            if (!entry.getKey().isConcrete()) {
//                falseReplacements.put(entry.getKey(), entry.getValue());
//            }
//        }
//        Set<LLVMHeuristicRelation> store = new LinkedHashSet<LLVMHeuristicRelation>(falseStateChangeInformation);
//        falseStateChangeInformation.clear();
//        for (LLVMHeuristicRelation rel : store) {
//            falseStateChangeInformation.add(rel.applySubstitution(unificationResult.y));
//        }
//    } else {
//        addingResult =
//            baseState.addRelations(
//                LLVMHeuristicIntegerState.getStrongestRelations(
//                    baseState,
//                    new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, secondRef, firstRef),
//                    params
//                ),
//                params
//            );
//        falseState = addingResult.x;
//        falseStateChangeInformation.addAll(addingResult.y);
//    }
//    return new Pair<LLVMAbstractState, LLVMAbstractState>(trueState, falseState);
//}

///**
// * @param state Some state.
// * @param stateChangeInformation The state change information.
// * @param replacements Replacements of references by other references.
// * @param params Strategy parameters.
// * @return The state emerging from the specified state by adding pointer inequalities, resolving reference
// *         equalities, and adjusting the values. Moreover, the set of learned relations and replacements conducted.
// */
//private static RefinementResult computeRefinementResult(
//    LLVMAbstractState state,
//    Collection<LLVMHeuristicRelation> stateChangeInformation,
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
//    LLVMParameters params
//) {
//    Pair<LLVMAbstractState, LLVMHeuristicRelationSet> pointerIneqs = state.addPointerInequalities(params);
//    stateChangeInformation.addAll(pointerIneqs.y);
//    ReplacementResult replacement = LLVMHeuristicIntegerState.resolveReferenceEqualities(pointerIneqs.x, params);
//    LLVMHeuristicExpressionUtils.updateReplacements(replacements, replacement.y);
//    KnowledgeResult adjusted = replacement.x.adjustValues(params);
//    LLVMHeuristicExpressionUtils.updateReplacements(replacements, adjusted.z);
//    for (Map.Entry<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> entry : adjusted.y.entrySet()) {
//        LLVMHeuristicVariable key = entry.getKey();
//        Pair<BigInteger, BigInteger> value = entry.getValue();
//        if (value.x != null) {
//            if (value.y != null) {
//                if (Globals.useAssertions) {
//                    assert (value.x.compareTo(value.y) < 0) : "Inconsistent value update!";
//                }
//                stateChangeInformation.add(
//                    new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, key, new LLVMHeuristicConstRef(value.y))
//                );
//                stateChangeInformation.add(
//                    new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, new LLVMHeuristicConstRef(value.x), key)
//                );
//            } else {
//                stateChangeInformation.add(
//                    new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, new LLVMHeuristicConstRef(value.x), key)
//                );
//            }
//        } else if (value.y != null) {
//            stateChangeInformation.add(
//                new LLVMHeuristicRelation(LLVMHeuristicRelationType.LE, key, new LLVMHeuristicConstRef(value.y))
//            );
//        }
//    }
//    Set<LLVMHeuristicRelation> store = new LinkedHashSet<LLVMHeuristicRelation>(stateChangeInformation);
//    stateChangeInformation.clear();
//    for (LLVMHeuristicRelation rel : store) {
//        stateChangeInformation.add(rel.applySubstitution(replacements));
//    }
//    Iterator<Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable>> it = replacements.entrySet().iterator();
//    while (it.hasNext()) {
//        Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> entry = it.next();
//        if (entry.getKey() instanceof LLVMHeuristicConstRef) {
//            it.remove();
//        }
//    }
//LLVMAbstractState newState = adjusted.x;
//newState = newState.findFurtherAssociations(stateChangeInformation, params);
//newState = newState.findFurtherInvariants(stateChangeInformation, params);
//return new RefinementResult(
//    newState.setRefined(true),
//    stateChangeInformation,
//    replacements
//);
//}

///**
// * If we have equations with only one variable, we can replace the variable by a constant. This method might leave
// * tautological relations which must be cleaned thereafter!
// * @param state Some state
// * @param aborter To check for abortions.
// * @return A pair of 1) a state with replaced references and dropped equations used to infer the replacement and 2)
// *         the replacement map.
// */
//private static ReplacementResult replaceReferencesByConstantsUsingUnitEquations(
//    LLVMAbstractState state,
//    Abortion aborter
//) {
//    // Get the current state and its relations:
//    LLVMAbstractState newState = state;
//    // Safe all replacements in this map:
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements = new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> newReplacements = new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
//    do {
//        aborter.checkAbortion();
//        LLVMHeuristicExpressionUtils.updateReplacements(replacements, newReplacements);
//        newReplacements.clear();
//        // Check whether there are relations from which we can infer knowledge and if so, do it:
//        for (LLVMHeuristicRelation rel : newState.getRelations()) {
//            if (!rel.isEquation()) {
//                continue;
//            }
//            /*
//             * We try to detect a relation containing only + and - with exactly one non-concrete reference
//             * occurring exactly once.
//             * TODO: Make it more general!
//             */
//            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> leftLinear = rel.getLhs().toLinear();
//            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rightLinear = rel.getRhs().toLinear();
//            LLVMHeuristicVariable variable;
//            LLVMHeuristicVariable constant;
//            if (leftLinear.x instanceof LLVMHeuristicVarRef) {
//                if (rightLinear.x != null || leftLinear.z.compareTo(BigInteger.ONE) != 0) {
//                    continue;
//                }
//                variable = (LLVMHeuristicVariable)leftLinear.x;
//                constant = new LLVMHeuristicConstRef(rightLinear.y.subtract(leftLinear.y));
//            } else if (rightLinear.x instanceof LLVMHeuristicVarRef) {
//                if (leftLinear.x != null || rightLinear.z.compareTo(BigInteger.ONE) != 0) {
//                    continue;
//                }
//                variable = (LLVMHeuristicVariable)rightLinear.x;
//                constant = new LLVMHeuristicConstRef(leftLinear.y.subtract(rightLinear.y));
//            } else {
//                continue;
//            }
//            // Substitute variable by constant and drop the unit equation:
//            LLVMHeuristicRelationSet newRels = new LLVMHeuristicRelationSet(newState.getRelations());
//            newRels.remove(rel);
//            newState = newState.setRelations(newRels).replaceSymbolicVariable(variable, constant);
//            // Finally, we have to safe the replacement:
//            LLVMHeuristicExpressionUtils.updateReplacements(newReplacements, Collections.singletonMap(variable, constant));
//        }
//    } while (!newReplacements.isEmpty());
//    return new ReplacementResult(newState, replacements);
//}

///**
// * We should not have to use this method, but since we want to maintain compatibility with the traditional LLVM
// * integer inference, we have to check for this.
// * @param state Some integerState, which may or may not be a LLVMIntegerState
// * @param useCache True if the integerState should use the unequalCache, false if it should not
// * @return If the given IntegerInterface is a LLVMIntegerState or a CompoundState that contains a LLVMIntegerState,
// * the useCache-flag is set on it. Otherwise, the given state is returned
// */
//private static IntegerState setUseCacheOnLLVMIntegerState(final IntegerState state, final boolean useCache)
//{
//    if (state instanceof LLVMIntegerState) {
//        return ((LLVMIntegerState) state).setUseCache(useCache);
//    } else if (state instanceof CompositeIntegerInterface) {
//        final List<IntegerState> newList = new LinkedList<>();
//        for (final IntegerState compoundState : ((CompositeIntegerInterface) state).getCompoundStates()) {
//            newList.add(LLVMHeuristicIntegerState.setUseCacheOnLLVMIntegerState(compoundState, useCache));
//        }
//        return CompositeIntegerInterface.build(newList);
//    } else {
//        return state;
//    }
//}

///**
// * If we know that two different references must be equal, just replace one by the other. This might leave
// * tautological relations which must be cleaned thereafter!
// * @param state Some state
// * @param params Strategy parameters.
// * @return A pair of a state with replaced references and the replacement map.
// */
//private static ReplacementResult unifyEqualReferences(LLVMAbstractState state, LLVMParameters params) {
//    // get the current state and its relations
//    LLVMAbstractState newState = state;
//    // safe all replacements in this map
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements = new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
//    Map<LLVMHeuristicVariable, LLVMHeuristicVariable> newReplacements = new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
//    outerloop: do {
//        params.aborter.checkAbortion();
//        LLVMHeuristicExpressionUtils.updateReplacements(replacements, newReplacements);
//        newReplacements.clear();
//        // check whether there are references that we know to be equal - if so, unify them
//        Set<LLVMHeuristicVariable> remainingRefs = new LinkedHashSet<LLVMHeuristicVariable>(newState.getValues().keySet());
//        for (LLVMHeuristicVariable ref1 : newState.getValues().keySet()) {
//            remainingRefs.remove(ref1);
//            for (LLVMHeuristicVariable ref2 : remainingRefs) {
//                YNM isEqual =
//                    this.truthValueOfRelation(
//                        newState,
//                        ref1,
//                        IntegerRelationType.EQ,
//                        ref2,
//                        true,
//                        params
//                    );
//                switch (isEqual) {
//                    case YES:
//                        // unify references
//                        ReplacementResult unifiedState = newState.unifySymbolicVariables(ref1, ref2, params);
//                        // substitute state by state with unified references
//                        newState = unifiedState.x;
//                        // update replacements
//                        newReplacements.putAll(unifiedState.y);
//                        // the references might have changed, so we have to break here
//                        continue outerloop;
//                    case NO:
//                        if (ref1 instanceof LLVMHeuristicVarRef && ref2 instanceof LLVMHeuristicVarRef) {
//                            newState = newState.addReferenceInequalities((LLVMHeuristicVarRef)ref1, (LLVMHeuristicVarRef)ref2);
//                        }
//                    default:
//                        // do nothing
//                }
//            }
//        }
//    } while (!newReplacements.isEmpty());
//    return new ReplacementResult(newState, replacements);
//}

