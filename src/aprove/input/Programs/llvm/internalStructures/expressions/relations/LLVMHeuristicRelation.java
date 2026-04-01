package aprove.input.Programs.llvm.internalStructures.expressions.relations;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A Relation models dependencies between two OpNodes.
 * @author Janine Repke, cryingshadow
 */
public final class LLVMHeuristicRelation extends LLVMRelation {

//  /**
//  * Checks whether phi follows from psi.
//  * Does Psi |= phi hold?
//  * @param psi A formula.
//  * @param phi Another formula.
//  * @return Yes, no, or maybe.
//  */
// public static YNM checkImplication(Formula<SMTLIBTheoryAtom> psi, Formula<SMTLIBTheoryAtom> phi) {
//     FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
//     try {
//         // is psi => phi satisfiable?, same like psi & !psi unsatisfiable
//         return (YNM) new YicesEngine().satisfiable(
//             Collections.singletonList(factory.buildAnd(psi, factory.buildNot(phi))),
//             SMTLogic.QF_LIA,
//             AbortionFactory.create()).not();
//     } catch (AbortionException | WrongLogicException e) {
//         return YNM.MAYBE;
//     }
// }

// /**
//  * Creates from a given relation set an SMT formula.
//  * @param relations The relations.
//  * @return An SMT formula representing the conjunction of the specified relations.
//  */
// public static Formula<SMTLIBTheoryAtom> createSMTFormula(Set<LLVMHeuristicRelation> relations) {
//     List<SMTLIBTheoryAtom> smtList = new LinkedList<SMTLIBTheoryAtom>();
//     for (LLVMHeuristicRelation relation : relations) {
//         smtList.add(relation.toSMTAtom());
//     }
//     FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
//     return factory.buildAnd(factory.buildTheoryAtoms(smtList));
// }

    /**
     * We have an equation (or suitable directed inequality) of the form left1 + left2 = right1 - right2. The question
     * is whether expr is in the desired relation with right1.
     * @param state The abstract state holding the knowledge about the references.
     * @param expr An expression.
     * @param left1 A reference.
     * @param left2 A reference.
     * @param right2 A reference.
     * @param strict Strict relation?
     * @param greater Greater or less than?
     * @return True if the relation holds by the values of the references. False otherwise.
     */
    private static boolean addSubPattern(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicTerm expr,
        LLVMHeuristicVariable left1,
        LLVMHeuristicVariable left2,
        LLVMHeuristicVariable right2,
        boolean strict,
        boolean greater
    ) {
        // only if the sign of right2 is clear, we can infer something
        AbstractBoundedInt valRight2 = state.getValue(right2).getThisAsAbstractBoundedInt();
        if (!greater && valRight2.isNonNegative()) {
            if (left1.equals(expr)) {
                return LLVMHeuristicRelation.addSubPatternHelp(state, left2, valRight2, strict, greater);
            } else if (left2.equals(expr)) {
                return LLVMHeuristicRelation.addSubPatternHelp(state, left1, valRight2, strict, greater);
            }
        } else if (greater && valRight2.isNonPositive()) {
            if (left1.equals(expr)) {
                return LLVMHeuristicRelation.addSubPatternHelp(state, left2, valRight2, strict, greater);
            } else if (left2.equals(expr)) {
                return LLVMHeuristicRelation.addSubPatternHelp(state, left1, valRight2, strict, greater);
            }
        }
        return false;
    }

    /**
     * We have an equation of the form exprRef + addRef = resRef - subRef. The question is whether exprRef rel resRef
     * holds where rel is a directed inequality.
     * @param state The abstract state containing the knowledge about the references.
     * @param addRef The reference in the addition.
     * @param subVal The value of the reference being subtracted.
     * @param strict Is the desired inequality strict?
     * @param greater Is the desired inequality a greater or less than relation?
     * @return True if the relation holds by the sign of the values of addRef and subRef. False otherwise.
     */
    private static boolean addSubPatternHelp(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicVariable addRef,
        AbstractBoundedInt subVal,
        boolean strict,
        boolean greater
    ) {
        AbstractBoundedInt val = state.getValue(addRef).getThisAsAbstractBoundedInt();
        if (greater) {
            if (strict) {
                if (val.isNegative() || (val.isNonPositive() && subVal.isNegative())) {
                    return true;
                }
            } else if (val.isNonPositive()) {
                return true;
            }
        } else {
            if (strict) {
                if (val.isPositive() || (val.isNonNegative() && subVal.isPositive())) {
                    return true;
                }
            } else if (val.isNonNegative()) {
                return true;
            }
        }
        return false;
    }

    /**
     * @param state The abstract state.
     * @param rels The relations.
     * @param from A reference.
     * @param to Another reference.
     * @param currentOffset The current offset.
     * @param visited Already visited LLVMReferences, collected to avoid infinite loops.
     *        For example, a loop occurs if we have inequalities v1 < v2 + 1 and v2 <= v1.
     * @param aborter To check for abortions.
     * @return For the biggest non-negative constant c such that from + c <= to, we return currentOffset + c. Null if
     *         no such offset exists.
     */
    private static BigInteger computeBiggestKnownOffsetBetween(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicVariable from,
        LLVMHeuristicVariable to,
        BigInteger currentOffset,
        Set<LLVMHeuristicVariable> visited,
        Abortion aborter
    ) {
        if (from.equals(to)) {
            return currentOffset;
        }
        if (visited.contains(from)) {
            // We have been there before...
            return null;
        }
        if (to.isConcrete() || from.isConcrete()) {
            return null;
        }
        // We add "from" to visited until we reach it again.
        visited.add(from);
        aborter.checkAbortion();
        BigInteger biggestOffset = null;
        for (LLVMHeuristicRelation rel : rels.getRelationsWithoutUndirectedInequalities()) {
            final BigInteger completeOffset;
            switch (rel.getRelationType()) {
            case EQ:
                Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger> pattern = rel.toOffByConstantPattern();
                if (pattern == null) {
                    continue;
                }
                BigInteger nextOffset;
                LLVMHeuristicVariable nextFrom;
                if (pattern.x.equals(from)) {
                    if (pattern.z.compareTo(BigInteger.ZERO) < 0) {
                        continue;
                    }
                    nextOffset = pattern.z;
                    nextFrom = pattern.y;
                } else if (pattern.y.equals(from)) {
                    if (pattern.z.compareTo(BigInteger.ZERO) > 0) {
                        continue;
                    }
                    nextOffset = pattern.z.negate();
                    nextFrom = pattern.x;
                } else {
                    continue;
                }
                completeOffset =
                    LLVMHeuristicRelation.computeBiggestKnownOffsetBetween(
                        state,
                        rels,
                        nextFrom,
                        to,
                        nextOffset,
                        visited,
                        aborter
                    );
                if (completeOffset == null) {
                    continue;
                }
                if (biggestOffset == null || completeOffset.compareTo(biggestOffset) > 0) {
                    biggestOffset = completeOffset;
                }
                break;
            case LE:
            case LT:
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
                if (lhsLinear.x == null || !lhsLinear.x.equals(from) || lhsLinear.z.compareTo(BigInteger.ONE) != 0) {
                    continue;
                }
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
                if (
                    rhsLinear.x == null
                    || !(rhsLinear.x instanceof LLVMHeuristicVariable)
                    || rhsLinear.z.compareTo(BigInteger.ONE) != 0
                ) {
                    continue;
                }
                completeOffset =
                    LLVMHeuristicRelation.computeBiggestKnownOffsetBetween(
                        state,
                        rels,
                        (LLVMHeuristicVariable)rhsLinear.x,
                        to,
                        rel.getHeuristicRelationType() == LLVMHeuristicRelationType.LT ?
                            lhsLinear.y.subtract(rhsLinear.y).add(BigInteger.ONE) :
                                lhsLinear.y.subtract(rhsLinear.y),
                        visited,
                        aborter
                    );
                if (completeOffset == null) {
                    continue;
                }
                if (biggestOffset == null || completeOffset.compareTo(biggestOffset) > 0) {
                    biggestOffset = completeOffset;
                }
                break;
            default:
                throw new IllegalStateException("How did this relation find its way into this loop?");
            }
        }
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs = state.getAssociations();
        if (assocs.containsKey(from)) {
            LLVMHeuristicVariable upperLimit = (LLVMHeuristicVariable)state.getAllocations().get(assocs.get(from)).y;
            if (upperLimit.equals(to)) {
                BigInteger associationOffset = state.getAssociationOffsets().get(from);
                if (biggestOffset == null || biggestOffset.compareTo(associationOffset) < 0) {
                    biggestOffset = associationOffset;
                }
            }
            if (!upperLimit.equals(from)) {
                BigInteger completeOffset =
                    LLVMHeuristicRelation.computeBiggestKnownOffsetBetween(
                        state,
                        rels,
                        upperLimit,
                        to,
                        BigInteger.ZERO,
                        visited,
                        aborter
                    );
                if (completeOffset != null && (biggestOffset == null || completeOffset.compareTo(biggestOffset) > 0)) {
                    biggestOffset = completeOffset;
                }
            }
        }
        return biggestOffset == null ? null : currentOffset.add(biggestOffset);
    }

    /**
     * We have an equation of the form expr = operation.
     * @param state The abstract state holding the knowledge about the references.
     * @param opType The operation type of the operation.
     * @param opLhs The left-hand side of the operation.
     * @param opRhs The right-hand side of the operation.
     * @param strict Strict relation?
     * @param greater Greater or less than?
     * @return A set of expressions (more precisely references here) known to be in the desired relation from expr.
     */
    private static Set<LLVMHeuristicTerm> handleExpressionEquation(
        LLVMHeuristicIntegerState state,
        ArithmeticOperationType opType,
        LLVMHeuristicVariable opLhs,
        LLVMHeuristicVariable opRhs,
        boolean strict,
        boolean greater
    ) {
        switch (opType) {
        case ADD:
            Set<LLVMHeuristicTerm> res = new LinkedHashSet<LLVMHeuristicTerm>();
            if (
                !opLhs.isConcrete()
                && LLVMHeuristicIntegerState.isInRelationByAddition(
                    state.getValue(opRhs).getThisAsAbstractBoundedInt(),
                    strict,
                    greater
                )
            ) {
                res.add(opLhs);
            }
            if (
                !opRhs.isConcrete()
                && LLVMHeuristicIntegerState.isInRelationByAddition(
                    state.getValue(opLhs).getThisAsAbstractBoundedInt(),
                    strict,
                    greater
                )
            ) {
                res.add(opRhs);
            }
            return res;
        case SUB:
            if (
                !opLhs.isConcrete()
                && LLVMHeuristicIntegerState.isInRelationBySubtraction(
                    state.getValue(opRhs).getThisAsAbstractBoundedInt(),
                    strict,
                    greater
                )
            ) {
                return Collections.<LLVMHeuristicTerm>singleton(opLhs);
            }
            break;
        default:
            // too complicated (for now)
        }
        return Collections.<LLVMHeuristicTerm>emptySet();
    }

    /**
     * Should not be used outside of factory methods (this is why it is package private).
     * @param relType The type of the relation.
     * @param left The left-hand side of the relation.
     * @param right The right-hand side of the relation.
     */
    LLVMHeuristicRelation(LLVMHeuristicRelationType relType, LLVMHeuristicTerm left, LLVMHeuristicTerm right) {
        super(relType.toIntegerRelationType(), left, right);
    }

    /**
     * Substitutes all occurrences of the reference oldVariable by the specified OpNode.
     * @param oldVariable Reference which will be replaced.
     * @param newNode The new node.
     * @return The substituted relation.
     */
    public LLVMHeuristicRelation applySubstitution(LLVMHeuristicVariable oldVariable, LLVMHeuristicTerm newNode) {
        return this.applySubstitution(Collections.singletonMap(oldVariable, newNode));
    }

    /**
     * Substitutes all references in the key set of the map by their values.
     * @param oldToNew Reference mapping.
     * @return The substituted relation.
     */
    @Override
    public LLVMHeuristicRelation applySubstitution(Map<? extends Variable, ? extends Expression> oldToNew) {
        return
            this.getRelationFactory().createRelation(
                this.getRelationType(),
                this.getLhs().applySubstitution(oldToNew),
                this.getRhs().applySubstitution(oldToNew)
            );
    }

    /**
     * If this method returns true, we can then get the relation through this.getStrictestSubsumingRelation(other).
     * @param other Some other Relation
     * @return True iff we can represent some relation ret such that (this || other) ==> ret.
     */
    public boolean canRepresentStrictestSubsumingRelation(LLVMHeuristicRelation other) {
        final boolean verbatimEqual = this.getLhs().equals(other.getLhs()) && this.getRhs().equals(other.getRhs());
        final boolean mirroredEqual = this.getLhs().equals(other.getRhs()) && this.getRhs().equals(other.getLhs());
        final boolean isSymmetrical =
            this.getHeuristicRelationType().isSymmetrical() || other.getHeuristicRelationType().isSymmetrical();
        final boolean compatibleSides = (verbatimEqual || (isSymmetrical && mirroredEqual));
        if (compatibleSides) {
            final boolean canRepresentSubsumingType =
                (this.getHeuristicRelationType().merge(other.getHeuristicRelationType()) != null);
            return canRepresentSubsumingType;
        } else {
            return false;
        }
    }

    /**
     * @return If this relation contains exactly one variable (and only once) and it just restricts the value of this
     *         variable, we return this variable, the value by which it is restricted, and a Boolean object encoding
     *         the direction of the restriction: null means equality, true that the value is greater than or equal to
     *         the variable, and false that the value is less than or equal to the variable. Null otherwise.
     */
    public Triple<LLVMHeuristicVariable, BigInteger, Boolean> checkValueRelation() {
        if (this.getNumberOfVarOccs() == 1) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = this.getLhs().toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = this.getRhs().toLinear();
            if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                assert (lhsLinear.x == null || rhsLinear.x == null) :
                    "Relation with only one reference has non-constant expressions on both sides.";
            }
            if (lhsLinear.x == null) {
                if (rhsLinear.x instanceof LLVMHeuristicVariable) {
                    BigInteger constantWithoutDivision = lhsLinear.y.subtract(rhsLinear.y);
                    switch (this.getRelationType()) {
                        case EQ:
                            return new Triple<LLVMHeuristicVariable, BigInteger, Boolean>(
                                (LLVMHeuristicVariable)rhsLinear.x,
                                constantWithoutDivision.divide(rhsLinear.z),
                                null
                            );
                        case LT:
                            constantWithoutDivision = constantWithoutDivision.add(BigInteger.ONE);
                            // fall through
                        case LE:
                            return new Triple<LLVMHeuristicVariable, BigInteger, Boolean>(
                                (LLVMHeuristicVariable)rhsLinear.x,
                                constantWithoutDivision.divide(rhsLinear.z),
                                false
                            );
                        default:
                            // do nothing - just fall through
                    }
                }
            } else if (lhsLinear.x instanceof LLVMHeuristicVariable) {
                BigInteger constantWithoutDivision = rhsLinear.y.subtract(lhsLinear.y);
                switch (this.getRelationType()) {
                    case EQ:
                        return new Triple<LLVMHeuristicVariable, BigInteger, Boolean>(
                            (LLVMHeuristicVariable)lhsLinear.x,
                            constantWithoutDivision.divide(lhsLinear.z),
                            null
                        );
                    case LT:
                        constantWithoutDivision = constantWithoutDivision.subtract(BigInteger.ONE);
                        // fall through
                    case LE:
                        return new Triple<LLVMHeuristicVariable, BigInteger, Boolean>(
                            (LLVMHeuristicVariable)lhsLinear.x,
                            constantWithoutDivision.divide(lhsLinear.z),
                            true
                        );
                    default:
                        // do nothing - just fall through
                }
            }
        }
        return null;
    }

    /**
     * @return The highest absolute constant multiplicative factor occurring in this relation.
     */
    public BigInteger computeHighestAbsoluteFactor() {
        return this.getLhs().computeHighestAbsoluteFactor().max(this.getRhs().computeHighestAbsoluteFactor());
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        LLVMHeuristicRelation other = (LLVMHeuristicRelation)obj;
        if (this.getHeuristicRelationType() != other.getHeuristicRelationType()) {
            return false;
        }
        switch (this.getHeuristicRelationType()) {
            case EQ:
            case NE:
                return
                    (this.getLhs().equals(other.getLhs()) && this.getRhs().equals(other.getRhs()))
                    || (this.getLhs().equals(other.getRhs()) && this.getRhs().equals(other.getLhs()));
            default:
                return this.getLhs().equals(other.getLhs()) && this.getRhs().equals(other.getRhs());
        }
    }

    /**
     * @return The variable that this relation provides a numerical bound for.
     *  Null if this relation does not provide a numerical bound for any
     *  variable.
     */
    public LLVMHeuristicVarRef getBoundedVariable() {
        final Triple<LLVMHeuristicVariable, BigInteger, Boolean> valueRelation = this.checkValueRelation();
        return valueRelation != null ? (LLVMHeuristicVarRef) valueRelation.x : null;
    }

    /**
     * @param ref Some reference.
     * @return An expression syntactically different from the specified reference, but known to be equal to it by this
     *         relation. Null if no such expression can be inferred.
     */
    public LLVMHeuristicTerm getEqualExpression(LLVMHeuristicVariable ref) {
        if (!this.isEquation()) {
            return null;
        }
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = this.getLhs().toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = this.getRhs().toLinear();
        if (ref.equals(lhsLinear.x)) {
            BigInteger offset = rhsLinear.y.subtract(lhsLinear.y);
            if (
                offset.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) != 0
                || (rhsLinear.x != null && rhsLinear.z.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) != 0)
            ) {
                return null;
            }
            return
                termFactory.create(
                    rhsLinear.x,
                    offset.divide(lhsLinear.z),
                    rhsLinear.x == null ? null : rhsLinear.z.divide(lhsLinear.z)
                );
        } else if (ref.equals(rhsLinear.x)) {
            BigInteger offset = lhsLinear.y.subtract(rhsLinear.y);
            if (
                offset.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) != 0
                || (lhsLinear.x != null && lhsLinear.z.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) != 0)
            ) {
                return null;
            }
            return
                termFactory.create(
                    lhsLinear.x,
                    offset.divide(rhsLinear.z),
                    lhsLinear.x == null ? null : lhsLinear.z.divide(rhsLinear.z)
                );
        }
        return null;
    }

    /**
     * @param state The abstract state holding the knowledge about the references.
     * @param knownRels The relations to consider for recursive inference.
     * @param expr A non-constant expression.
     * @param strict Flag indicating whether we look for a strict or weak inequality.
     * @param greater Flag indicating whether we look for a greater or less than inequality.
     * @param params Strategy parameters.
     * @return A set of expressions known to be in the desired relation from the specified expression just by this
     *         relation (e.g., if x is in the returned set and strict and greater are true, then we have expr > x). The
     *         specified expression itself is not necessarily contained in this set, even for weak inequalities.
     */
    public Set<LLVMHeuristicTerm> getExpressionsInDirectedInequality(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicRelationSet knownRels,
        LLVMHeuristicTerm expr,
        boolean strict,
        boolean greater,
        LLVMParameters params,
        Abortion aborter
    ) {
        if (this.getHeuristicRelationType() == LLVMHeuristicRelationType.NE) {
            // for undirected inequalities, we cannot infer anything
            return Collections.<LLVMHeuristicTerm>emptySet();
        }
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        final boolean strictNeeded = strict && this.getHeuristicRelationType() != LLVMHeuristicRelationType.LT;
        Set<LLVMHeuristicTerm> res = new LinkedHashSet<LLVMHeuristicTerm>();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
        if (exprLinear.x == null) {
            return Collections.<LLVMHeuristicTerm>emptySet();
        }
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = this.getLhs().toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = this.getRhs().toLinear();
        LLVMHeuristicTerm exprWithoutOffset =
            termFactory.create(ArithmeticOperationType.MUL, termFactory.constant(exprLinear.z), exprLinear.x);
        LLVMHeuristicTerm lhsWithoutOffset =
            lhsLinear.x == null ?
                null :
                    termFactory.create(ArithmeticOperationType.MUL, termFactory.constant(lhsLinear.z), lhsLinear.x);
        LLVMHeuristicTerm rhsWithoutOffset =
            rhsLinear.x == null ?
                null :
                    termFactory.create(ArithmeticOperationType.MUL, termFactory.constant(rhsLinear.z), rhsLinear.x);
        if (exprWithoutOffset == null || (lhsWithoutOffset == null && rhsWithoutOffset == null)) {
            // we only need to infer something if neither the expression nor the relation is just about constants
            return Collections.<LLVMHeuristicTerm>emptySet();
        }
        if (
            (!greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ)
            && exprWithoutOffset.equals(lhsWithoutOffset)
        ) {
            BigInteger totalOffset;
            if (!strict && this.getHeuristicRelationType() == LLVMHeuristicRelationType.LT) {
                totalOffset = rhsLinear.y.subtract(BigInteger.ONE).add(exprLinear.y).subtract(lhsLinear.y);
            } else if (strictNeeded) {
                if (greater) {
                    totalOffset = rhsLinear.y.subtract(BigInteger.ONE).add(exprLinear.y).subtract(lhsLinear.y);
                } else {
                    totalOffset = rhsLinear.y.add(BigInteger.ONE).add(exprLinear.y).subtract(lhsLinear.y);
                }
            } else {
                totalOffset = rhsLinear.y.add(exprLinear.y).subtract(lhsLinear.y);
            }
            res.add(
                termFactory.create(ArithmeticOperationType.ADD, termFactory.constant(totalOffset), rhsWithoutOffset)
            );
        }
        if (
            (greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ)
            && exprWithoutOffset.equals(rhsWithoutOffset)
        ) {
            BigInteger totalOffset;
            if (!strict && this.getHeuristicRelationType() == LLVMHeuristicRelationType.LT) {
                totalOffset = lhsLinear.y.add(BigInteger.ONE).add(exprLinear.y).subtract(rhsLinear.y);
            } else if (strictNeeded) {
                if (greater) {
                    totalOffset = lhsLinear.y.subtract(BigInteger.ONE).add(exprLinear.y).subtract(rhsLinear.y);
                } else {
                    totalOffset = lhsLinear.y.add(BigInteger.ONE).add(exprLinear.y).subtract(rhsLinear.y);
                }
            } else {
                totalOffset = lhsLinear.y.add(exprLinear.y).subtract(rhsLinear.y);
            }
            res.add(
                termFactory.create(ArithmeticOperationType.ADD, termFactory.constant(totalOffset), lhsWithoutOffset)
            );
        }
        if (this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ) {
            // here, we really want to use expr
            this.handleEquationWithValues(state, expr, res, strictNeeded, greater);
        }
        if (this.getLhs() instanceof LLVMHeuristicOperation && this.getRhs() instanceof LLVMHeuristicOperation) {
            this.handleComplexRelation(state, knownRels, expr, res, strictNeeded, greater, params, aborter);
        }
        if (!(exprWithoutOffset instanceof LLVMHeuristicVariable)) {
            this.handleLiteralsInExpression(expr, res, strict, greater);
        }
        if (
            rhsWithoutOffset instanceof LLVMHeuristicOperation
            && (
                this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ
                || (greater && exprLinear.z.compareTo(BigInteger.ZERO) > 0)
                || (!greater && exprLinear.z.compareTo(BigInteger.ZERO) < 0)
            )
        ) {
            this.handleLiteralsInRelation(
                res,
                exprLinear,
                this.getLhs(),
                this.getRhs().getLiterals(),
                strict,
                greater,
                this.getHeuristicRelationType() == LLVMHeuristicRelationType.LT
            );
        }
        if (
            lhsWithoutOffset instanceof LLVMHeuristicOperation
            && (
                this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ
                || (greater && exprLinear.z.compareTo(BigInteger.ZERO) < 0)
                || (!greater && exprLinear.z.compareTo(BigInteger.ZERO) > 0)
            )
        ) {
            this.handleLiteralsInRelation(
                res,
                exprLinear,
                this.getRhs(),
                this.getLhs().getLiterals(),
                strict,
                greater,
                this.getHeuristicRelationType() == LLVMHeuristicRelationType.LT
            );
        }
        return res;
    }

    /**
     * @return The type of this relation.
     */
    public LLVMHeuristicRelationType getHeuristicRelationType() {
        return LLVMHeuristicRelationType.fromIntegerRelationType(super.getRelationType());
    }

    @Override
    public LLVMHeuristicTerm getLhs() {
        return (LLVMHeuristicTerm)super.getLhs();
    }

    /**
     * The variable that is bounded with this bound can be found by
     *  getBoundedVariable()
     * @return The lower bound of some variable specified by this relation.
     *  Null if this relation does not specify a numerical lower bound for a
     *  single variable.
     */
    public BigInteger getLowerBound() {
        if (this.isLowerBoundRelation()) {
            return this.checkValueRelation().y;
        } else {
            return null;
        }
    }

    /**
     * @return The number of positions within this relation holding a variable.
     */
    public int getNumberOfVarOccs() {
        return this.getLhs().getNumberOfVarOccs() + this.getRhs().getNumberOfVarOccs();
    }

    @Override
    public LLVMHeuristicTerm getRhs() {
        return (LLVMHeuristicTerm)super.getRhs();
    }

    /**
     * @param other Some other relation
     * @return The strictest relation ret such that (this || other) ==> ret.
     *  Null if that relation is not representable.
     */
    public LLVMHeuristicRelation getStrictestSubsumingRelation(final LLVMHeuristicRelation other) {
        final boolean verbatimEqual = this.getLhs().equals(other.getLhs()) && this.getRhs().equals(other.getRhs());
        final boolean mirroredEqual = this.getLhs().equals(other.getRhs()) && this.getRhs().equals(other.getLhs());
        final boolean thisIsSymmetrical = this.getHeuristicRelationType().isSymmetrical();
        final boolean otherIsSymmetrical = other.getHeuristicRelationType().isSymmetrical();
        /* We currently have two possibilities to compute the strictest
         * subsuming relation. Either the left- and right-hand sides are
         * exactly equal, in which case we can just merge the relation types.
         * This is the ``verbatimEqual''-part of the condition.
         * The other case is that one of the relations is symmetrical, but
         * mirrored (consider, e.g., x == y and y == x). This is the
         * ``isSymmetrical && mirroredEqual''-part of the condition.
         */
        LLVMHeuristicTerm lhs = null, rhs = null;
        LLVMHeuristicRelationType relationType = null;
        if (verbatimEqual) {
            /* In this case it does not really matter if we take this.lhs and
             * this.rhs or other.lhs and other.rhs, since both are equal to
             * each other */
            lhs = this.getLhs();
            rhs = this.getRhs();
            relationType = this.getHeuristicRelationType().merge(other.getHeuristicRelationType());
        } else if (mirroredEqual) {
            if (thisIsSymmetrical) {
                /* Since this is a symmetrical relation, we have to take the
                 * lhs/rhs-order of the other relation in order to be able to
                 * use the result of getStrictestSubsumingType directly, since
                 * we may not be able to mirror the other relation */
                lhs = other.getLhs();
                rhs = other.getRhs();
                relationType = this.getHeuristicRelationType().merge(other.getHeuristicRelationType());
            } else if (otherIsSymmetrical) {
                /* The same reasoning as above applies here, with the only
                 * difference being that at this point we *know* that this is
                 * not symmetric */
                lhs = this.getLhs();
                rhs = this.getRhs();
                relationType = this.getHeuristicRelationType().merge(other.getHeuristicRelationType());
            }
        }
        if (relationType != null) {
            return this.getRelationFactory().createRelation(relationType, lhs, rhs);
        } else {
            return null;
        }
    }

    /**
     * The variable that is bounded with this bound can be found by
     *  getBoundedVariable()
     * @return The upper bound of some variable specified by this relation.
     *  Null if this relation does not specify a numerical upper bound for a
     *  single variable.
     */
    public BigInteger getUpperBound() {
        if (this.isUpperBoundRelation()) {
            return this.checkValueRelation().y;
        } else {
            return null;
        }
    }

    /**
     * @return A set of all symbolic variables (including constant references) occurring in this relation.
     */
    @Override
    public Set<? extends LLVMHeuristicVariable> getVariables() {
        return this.getVariables(true);
    }

    /**
     * @param includeConstants Flag indicating whether or not constants should be included.
     * @return A set of all symbolic variables occurring in this relation.
     */
    public Set<LLVMHeuristicVariable> getVariables(boolean includeConstants) {
        Set<LLVMHeuristicVariable> res =
            new LinkedHashSet<LLVMHeuristicVariable>(this.getLhs().getVariables(includeConstants));
        res.addAll(this.getRhs().getVariables(includeConstants));
        return res;
    }

    /**
     * @param expr An expression which is not only a reference.
     * @param res The set of expressions known to be in the desired relation from expr.
     * @param strict Strict relation?
     * @param greater Greater or less than?
     */
    public void handleLiteralsInExpression(
        LLVMHeuristicTerm expr,
        Set<LLVMHeuristicTerm> res,
        boolean strict,
        boolean greater
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        List<LLVMHeuristicTerm> literals = expr.getLiterals();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = this.getLhs().toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = this.getRhs().toLinear();
        for (int i = 0; i < literals.size(); i++) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = literals.get(i).toLinear();
            if (linear.x == null) {
                continue;
            }
            if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                assert (linear.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
            }
            if (
                linear.x.equals(lhsLinear.x)
                && (
                    this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ
                    || (greater && lhsLinear.z.signum() != linear.z.signum())
                    || (!greater && lhsLinear.z.signum() == linear.z.signum())
                )
            ) {
                /*
                 * we have:
                 * lhsLinear.z * linear.x + lhsLinear.y <= rhsLinear.z * rhsLinear.x + rhsLinear.y
                 * and an expression
                 * x1 + x2 +...+ linear.z * linear.x +...
                 *
                 * if (sign(linear.z) == sign(lhsLinear.z)):
                 * linear.z * linear.x <=
                 *   (linear.z * rhsLinear.z / lhsLinear.z) * rhsLinear.x
                 *   + (linear.z * (rhsLinear.y - lhsLinear.y) / lhsLinear.z)
                 * else other direction
                 */
                // TODO check this
                if (rhsLinear.z == null) {
                    return;
                }
                BigInteger dividend1 = linear.z.multiply(rhsLinear.z);
                BigInteger dividend2 = rhsLinear.y.subtract(lhsLinear.y);
                if (!strict && this.getHeuristicRelationType() == LLVMHeuristicRelationType.LT) {
                    // we can infer a better bound - do it early to use the multiplicative factor
                    // lhsLinear.z * linear.x + lhsLinear.y < rhsLinear.z * rhsLinear.x + rhsLinear.y
                    // implies
                    // lhsLinear.z * linear.x + lhsLinear.y <= rhsLinear.z * rhsLinear.x + rhsLinear.y - 1
                    dividend2 = dividend2.subtract(BigInteger.ONE);
                }
                dividend2 = dividend2.multiply(linear.z);
                BigInteger divisorAbs = lhsLinear.z.abs();
                if (
                    dividend1.abs().remainder(divisorAbs).compareTo(BigInteger.ZERO) == 0
                    && dividend2.abs().remainder(divisorAbs).compareTo(BigInteger.ZERO) == 0
                ) {
                    // here, integer division is equivalent to division on reals
                    BigInteger offset = dividend2.divide(lhsLinear.z);
                    if (strict && this.getHeuristicRelationType() != LLVMHeuristicRelationType.LT) {
                        // we need to infer a worse bound - do it lately to avoid a bigger error by multiplication
                        if (greater) {
                            offset = offset.subtract(BigInteger.ONE);
                        } else {
                            offset = offset.add(BigInteger.ONE);
                        }
                    }
                    res.add(
                        this.buildExpression(
                            literals,
                            i,
                            termFactory.create(
                                ArithmeticOperationType.MUL,
                                termFactory.constant(dividend1.divide(lhsLinear.z)),
                                rhsLinear.x
                            ),
                            offset
                        )
                    );
                }
            }
            if (
                linear.x.equals(rhsLinear.x)
                && (
                    this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ
                    || (greater && rhsLinear.z.signum() == linear.z.signum())
                    || (!greater && rhsLinear.z.signum() != linear.z.signum())
                )
            ) {
                /*
                 * we have:
                 * lhsLinear.z * lhsLinear.x + lhsLinear.y <= rhsLinear.z * linear.x + rhsLinear.y
                 * and an expression
                 * x1 + x2 +...+ linear.z * linear.x +...
                 *
                 * if (sign(linear.z) == sign(rhsLinear.z)):
                 * linear.z * linear.x >=
                 *   (linear.z * lhsLinear.z / rhsLinear.z) * lhsLinear.x
                 *   + (linear.z * (lhsLinear.y - rhsLinear.y) / rhsLinear.z)
                 * else other direction
                 */
                // TODO check this
                if (lhsLinear.z == null) {
                    return;
                }
                BigInteger dividend1 = linear.z.multiply(lhsLinear.z);
                BigInteger dividend2 = lhsLinear.y.subtract(rhsLinear.y);
                if (!strict && this.getHeuristicRelationType() == LLVMHeuristicRelationType.LT) {
                    // we can infer a better bound - do it early to use the multiplicative factor
                    // lhsLinear.z * lhsLinear.x + lhsLinear.y < rhsLinear.z * linear.x + rhsLinear.y
                    // implies
                    // lhsLinear.z * lhsLinear.x + lhsLinear.y + 1 <= rhsLinear.z * linear.x + rhsLinear.y
                    dividend2 = dividend2.add(BigInteger.ONE);
                }
                dividend2 = dividend2.multiply(linear.z);
                BigInteger divisorAbs = rhsLinear.z.abs();
                if (
                    dividend1.abs().remainder(divisorAbs).compareTo(BigInteger.ZERO) == 0
                    && dividend2.abs().remainder(divisorAbs).compareTo(BigInteger.ZERO) == 0
                ) {
                    // here, integer division is equivalent to division on reals
                    BigInteger offset = dividend2.divide(rhsLinear.z);
                    if (strict && this.getHeuristicRelationType() != LLVMHeuristicRelationType.LT) {
                        // we need to infer a worse bound - do it lately to avoid a bigger error by multiplication
                        if (greater) {
                            offset = offset.subtract(BigInteger.ONE);
                        } else {
                            offset = offset.add(BigInteger.ONE);
                        }
                    }
                    res.add(
                        this.buildExpression(
                            literals,
                            i,
                            termFactory.create(
                                ArithmeticOperationType.MUL,
                                termFactory.constant(dividend1.divide(rhsLinear.z)),
                                lhsLinear.x
                            ),
                            offset
                        )
                    );
                }
            }
        }
    }

    /**
     * @param res The set of expressions known to be in the desired relation from expr.
     * @param exprLinear The non-constant expression expr decomposed into linear components.
     * @param otherSide One side of a relation which is not the side containing the literals.
     * @param literals The literals on the side of a relation to check for a match with expr.
     * @param strict Strict relation?
     * @param greater Greater relation?
     * @param lt Is the relation a less than relation?
     */
    public void handleLiteralsInRelation(
        Set<LLVMHeuristicTerm> res,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear,
        LLVMHeuristicTerm otherSide,
        List<LLVMHeuristicTerm> literals,
        boolean strict,
        boolean greater,
        boolean lt
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        for (LLVMHeuristicTerm literal : literals) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = literal.toLinear();
            if (
                !exprLinear.x.equals(linear.x)
                || exprLinear.z.abs().remainder(linear.z.abs()).compareTo(BigInteger.ZERO) != 0
            ) {
                continue;
            }
            if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                assert (linear.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
            }
            // greater case with positive factor:
            // otherSide <= x1 + x2 +...+ linear.z * exprLinear.x +...
            // exprLinear.z * exprLinear.x + exprLinear.y
            LLVMHeuristicTerm replacement = otherSide;
            for (LLVMHeuristicTerm otherLiteral : literals) {
                if (otherLiteral == literal) {
                    continue;
                }
                replacement = termFactory.create(ArithmeticOperationType.SUB, replacement, otherLiteral);
            }
            // now: replacement = otherSide - x1 - x2 -... (without linear.z * exprLinear.x)
            // exprLinear.x >= replacement / linear.z
            // exprLinear.z * (replacement / linear.z) + exprLinear.y
            BigInteger offset = exprLinear.y;
            if (strict && !lt) {
                if (greater) {
                    offset = offset.subtract(BigInteger.ONE);
                } else {
                    offset = offset.add(BigInteger.ONE);
                }
            } else if (!strict && lt) {
                if (greater) {
                    offset = offset.add(BigInteger.ONE);
                } else {
                    offset = offset.subtract(BigInteger.ONE);
                }
            }
            res.add(
                termFactory.create(
                    ArithmeticOperationType.ADD,
                    termFactory.constant(offset),
                    termFactory.create(
                        ArithmeticOperationType.MUL,
                        termFactory.constant(exprLinear.z.divide(linear.z)),
                        replacement
                    )
                )
            );
        }
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        int prime = 29;
        int result = 1;
        result =
            prime
            * result
            + ((this.getLhs() == null) ? 0 : this.getLhs().hashCode())
            + ((this.getRhs() == null) ? 0 : this.getRhs().hashCode());
        result =
            prime * result
            + ((this.getHeuristicRelationType() == null) ? 0 : this.getHeuristicRelationType().ordinal());
        return result;
    }

    /**
     * @return True iff this relation is of the form v rel c, where v is some
     * variable reference and c is some constant
     */
    public boolean isBoundingRelation() {
        return this.checkValueRelation() != null;
    }

    /**
     * @return True if this is an LT or an LE relation. False otherwise.
     */
    @Override
    public boolean isDirectedInequality() {
        switch (this.getHeuristicRelationType()) {
            case LT:
            case LE:
                return true;
            default:
                return false;
        }
    }

    /**
     * @return True if this relation provides a lower bound for a single variable.
     */
    public boolean isLowerBoundRelation() {
        final Triple<LLVMHeuristicVariable, BigInteger, Boolean> valueRelation = this.checkValueRelation();
        if (valueRelation == null) {
            return false;
        } else {
            return valueRelation.z == null || valueRelation.z == false;
        }
    }

    /**
     * @return True iff this relation is of the form ref1 relType ref2.
     */
    public boolean isSimple() {
        return this.getLhs() instanceof LLVMHeuristicVariable && this.getRhs() instanceof LLVMHeuristicVariable;
    }

    /**
     * @return True if this is an equation with only one operation: a) x = y op z or b) x op y = z.
     */
    public boolean isSimpleArithmeticEquation() {
        return
            this.isEquation()
            && (
                (
                    (this.getLhs() instanceof LLVMHeuristicVariable)
                    && (this.getRhs() instanceof LLVMHeuristicOperation)
                    && (((LLVMHeuristicOperation)this.getRhs()).isSimple())
                ) || (
                    (this.getRhs() instanceof LLVMHeuristicVariable)
                    && (this.getLhs() instanceof LLVMHeuristicOperation)
                    && (((LLVMHeuristicOperation)this.getLhs()).isSimple())
                )
            );
    }

    /**
     * @param params Strategy parameters.
     * @return True if this is a simple equation, like x = y. False otherwise.
     */
    public boolean isSimpleEquation() {
        return this.isEquation() && this.isSimple();
    }

    /**
     * @return True iff this relation is of type NE or LT.
     */
    @Override
    public boolean isStrictInequality() {
        switch (this.getHeuristicRelationType()) {
            case NE:
            case LT:
                return true;
            default:
                return false;
        }
    }

    /**
     * @return True if this relation provides an upper bound for a single
     *  variable
     */
    public boolean isUpperBoundRelation() {
        final Triple<LLVMHeuristicVariable, BigInteger, Boolean> valueRelation = this.checkValueRelation();
        if (valueRelation == null) {
            return false;
        } else {
            return valueRelation.z == null || valueRelation.z == true;
        }
    }

    /**
     * @return A new relation that holds if and only if this relation does not hold
     */
    @Override
    public LLVMHeuristicRelation negate() {
        switch (this.getHeuristicRelationType()) {
            case EQ:
                return this.getRelationFactory().createRelation(LLVMHeuristicRelationType.NE, this.getLhs(), this.getRhs());
            case LE:
                return this.getRelationFactory().createRelation(LLVMHeuristicRelationType.LT, this.getRhs(), this.getLhs());
            case LT:
                return this.getRelationFactory().createRelation(LLVMHeuristicRelationType.LE, this.getRhs(), this.getLhs());
            case NE:
                return this.getRelationFactory().createRelation(LLVMHeuristicRelationType.EQ, this.getLhs(), this.getRhs());
            default:
                throw new IllegalStateException("Someone found a new heuristic relation type!");
        }
    }

    @Override
    public LLVMHeuristicRelation setArguments(ImmutableList<? extends Expression> args) {
        assert (args.size() == 2) : "A binary expression must have exactly two arguments!";
        return
            this.getRelationFactory().createRelation(
                this.getRelationType(),
                (LLVMHeuristicTerm)args.get(0),
                (LLVMHeuristicTerm)args.get(1)
            );
    }

    /**
     * @param ref Some reference.
     * @return An expression known to be in relation to <code>ref</code> and a Boolean flag indicating the type of the
     *         relation (<code>null</code> means equality, <code>true</code> means the reference is greater than or
     *         equal to the expression, and <code>false</code> means the reference if less than or equal to the
     *         expression - the latter two possibilities are only considered if this relation is a directed inequality
     *         and nothing is "dropped" from this relation to compute the expression in relation to <code>ref</code>).
     */
    public Pair<LLVMHeuristicTerm, Boolean> solveFor(LLVMHeuristicVariable ref) {
        if (this.getHeuristicRelationType() == LLVMHeuristicRelationType.NE || ref instanceof LLVMHeuristicConstRef) {
            return null;
        }
        List<LLVMHeuristicTerm> leftLits = this.getLhs().getLiterals();
        List<LLVMHeuristicTerm> rightLits = this.getRhs().getLiterals();
        BigInteger divisor = null;
        int indexOfRef = 0;
        for (LLVMHeuristicTerm expr : leftLits) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
            if (ref.equals(exprLinear.x)) {
                if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                    assert (exprLinear.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
                }
                divisor = exprLinear.z;
                break;
            }
            indexOfRef++;
        }
        if (divisor == null) {
            indexOfRef = 0;
            for (LLVMHeuristicTerm expr : rightLits) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
                if (ref.equals(exprLinear.x)) {
                    if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                        assert (exprLinear.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
                    }
                    divisor = exprLinear.z;
                    break;
                }
                indexOfRef++;
            }
            if (divisor == null) {
                // relation is too complex
                return null;
            }
            return this.buildExpression(ref, leftLits, rightLits, divisor, indexOfRef, false);
        } else {
            return this.buildExpression(ref, rightLits, leftLits, divisor, indexOfRef, true);
        }
    }

    /**
     * @param ref Some reference.
     * @param val The value of the reference.
     * @return An expression known to be in relation to <code>ref</code> and the Boolean flag indicating the type of
     *         the relation, if relation is of the form c1 = (c2 + ref) mod c3, where c1 to c3 are constants, else null.
     */
    public Pair<LLVMHeuristicTerm, Boolean> solveModuloNormalForm(LLVMHeuristicVariable ref, LLVMValue val) {
        if (this.getLhs() instanceof LLVMHeuristicConstRef && this.getRhs() instanceof LLVMHeuristicOperation) {
            LLVMHeuristicOperation modExpr = (LLVMHeuristicOperation)this.getRhs();
            if (this.isEquation()) {
                if (
                    modExpr.getOperation() == ArithmeticOperationType.EMOD
                    && modExpr.getRhs() instanceof LLVMHeuristicConstRef
                ) {
                    // relation is of the form 'c1 = expression mod c2'
                    if (modExpr.getLhs() instanceof LLVMHeuristicOperation) {
                        LLVMHeuristicOperation modLhs = (LLVMHeuristicOperation)modExpr.getLhs();
                        if (
                            modLhs.getOperation() != ArithmeticOperationType.ADD
                            && modLhs.getOperation() != ArithmeticOperationType.SUB
                        ) {
                            return null;
                        }
                    }
                    // relation is of the form 'c1 = expression mod c2' where expression is an addition or subtraction
                    LLVMHeuristicConstRef modRhs = (LLVMHeuristicConstRef) modExpr.getRhs();
                    LLVMHeuristicRelation relWithoutMod =
                        LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY.createRelation(
                            IntegerRelationType.EQ,
                            this.getLhs(),
                            modExpr.getLhs()
                        );
                    // solve 'c1 = expression' instead
                    Pair<LLVMHeuristicTerm, Boolean> resWithoutMod = relWithoutMod.solveFor(ref);
                    if (resWithoutMod == null) {
                        return null;
                    }
                    if (resWithoutMod.x instanceof LLVMHeuristicConstRef) {
                        LLVMHeuristicConstRef res = (LLVMHeuristicConstRef)resWithoutMod.x;
                        BigInteger resAsInt = res.getIntegerValue();
                        BigInteger lower = val.getThisAsAbstractBoundedInt().getLower().getConstant();
                        BigInteger upper = val.getThisAsAbstractBoundedInt().getUpper().getConstant();
                        // now we have to adjust the value into its bounds
                        while (resAsInt.compareTo(lower) < 0) {
                            resAsInt = resAsInt.add(modRhs.getIntegerValue());
                        }
                        while (resAsInt.compareTo(upper) > 0) {
                            resAsInt = resAsInt.subtract(modRhs.getIntegerValue());
                        }
                        if (resAsInt.compareTo(lower) >= 0) {
                            return new Pair<LLVMHeuristicTerm, Boolean>(this.getTermFactory().constant(resAsInt), null);
                        }
                    }
                }
                // right hand side of relation is not a modulo operation
            }
            // relation is not an equation (could be implemented, if needed)
        }
        // relation not in desired form
        return null;
    }

    /**
     * @return A triple containing two references r1 and r2 and an offset o such that r2 = r1 + o if the relation
     *         implies this. If not, null is returned.
     */
    public Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger> toOffByConstantPattern() {
        if (!this.isEquation()) {
            return null;
        }
        if (this.getLhs() instanceof LLVMHeuristicVariable && this.getRhs() instanceof LLVMHeuristicOperation) {
            Pair<LLVMHeuristicVariable, BigInteger> pattern =
                ((LLVMHeuristicOperation)this.getRhs()).isOffByConstantPattern();
            if (pattern != null) {
                return new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger>(
                    pattern.x,
                    (LLVMHeuristicVariable)this.getLhs(),
                    pattern.y);
            }
        } else if (this.getRhs() instanceof LLVMHeuristicVariable && this.getLhs() instanceof LLVMHeuristicOperation) {
            Pair<LLVMHeuristicVariable, BigInteger> pattern =
                ((LLVMHeuristicOperation)this.getLhs()).isOffByConstantPattern();
            if (pattern != null) {
                return
                    new Triple<LLVMHeuristicVariable, LLVMHeuristicVariable, BigInteger>(
                        pattern.x,
                        (LLVMHeuristicVariable)this.getRhs(),
                        pattern.y
                    );
            }
        }
        return null;
    }

    @Override
    protected LLVMHeuristicRelationFactory getRelationFactory() {
        return LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY;
    }

    @Override
    protected LLVMHeuristicTermFactory getTermFactory() {
        return this.getRelationFactory().getTermFactory();
    }

    /**
     * We have a relation of the form left1 + left2 =/<=/< right1 + right2. The question is for which ref in
     * {left1,left2,right1,right2} we have expr rel ref where rel is defined by the specified boolean flags. We might
     * also add/subtract a constant one in case we are looking for a weak relation.
     * @param state The abstract state holding the knowledge about the references.
     * @param knownRels The relations to consider.
     * @param expr An expression.
     * @param left The left-hand side references.
     * @param right The right-hand side references.
     * @param strict Strict relation?
     * @param greater Greater than relation?
     * @param params Strategy parameters.
     * @return A set of expressions (more precisely references here) known to be in the desired relation.
     */
    private Set<LLVMHeuristicTerm> addAddPattern(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicRelationSet knownRels,
        LLVMHeuristicTerm expr,
        Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> left,
        Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> right,
        boolean strict,
        boolean greater,
        LLVMParameters params,
        Abortion aborter
    ) {
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
        if (exprLinear.x == null || exprLinear.z.compareTo(BigInteger.ONE) != 0) {
            // we have a constant or a multiplicative term - don't do the complicated reasoning
            return Collections.<LLVMHeuristicTerm>emptySet();
        }
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        boolean mirror;
        LLVMHeuristicVariable exprRef;
        LLVMHeuristicVariable sameSide;
        LLVMHeuristicVariable other1;
        LLVMHeuristicVariable other2;
        if ((!greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ) && left.x.equals(exprLinear.x)) {
            exprRef = left.x;
            sameSide = left.y;
            other1 = right.x;
            other2 = right.y;
            mirror = false;
        } else if (
            (!greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ) && left.y.equals(exprLinear.x)
        ) {
            exprRef = left.y;
            sameSide = left.x;
            other1 = right.x;
            other2 = right.y;
            mirror = false;
        } else if (
            (greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ) && right.x.equals(exprLinear.x)
        ) {
            exprRef = right.x;
            sameSide = right.y;
            other1 = left.x;
            other2 = left.y;
            mirror = true;
        } else if (
            (greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ) && right.y.equals(exprLinear.x)
        ) {
            exprRef = right.y;
            sameSide = right.x;
            other1 = left.x;
            other2 = left.y;
            mirror = true;
        } else {
            exprRef = null;
            sameSide = null;
            other1 = null;
            other2 = null;
            mirror = false;
        }
        if (exprRef != null) {
            Set<LLVMHeuristicTerm> res = new LinkedHashSet<LLVMHeuristicTerm>();
            LLVMHeuristicRelationSet next = new LLVMHeuristicRelationSet(knownRels);
            next.remove(this);
            IntegerRelationType relType = IntegerRelationType.create(strict, greater);
            BigInteger biggestOffsetFromOther1 =
                mirror ?
                    LLVMHeuristicRelation.computeBiggestKnownOffsetBetween(
                        state,
                        next,
                        sameSide,
                        other1,
                        BigInteger.ZERO,
                        new LinkedHashSet<LLVMHeuristicVariable>(),
                        aborter
                    ) :
                        LLVMHeuristicRelation.computeBiggestKnownOffsetBetween(
                            state,
                            next,
                            other1,
                            sameSide,
                            BigInteger.ZERO,
                            new LinkedHashSet<LLVMHeuristicVariable>(),
                            aborter
                        );
            if (biggestOffsetFromOther1 != null) {
                if (biggestOffsetFromOther1.compareTo(BigInteger.ZERO) != 0) {
                    res.add(
                        termFactory.create(
                            ArithmeticOperationType.ADD,
                            other2,
                            termFactory.constant(greater ? biggestOffsetFromOther1 : biggestOffsetFromOther1.negate())
                        )
                    );
                } else {
                    res.add(other2);
                }
            }
            BigInteger biggestOffsetFromOther2 =
                mirror ?
                    LLVMHeuristicRelation.computeBiggestKnownOffsetBetween(
                        state,
                        next,
                        sameSide,
                        other2,
                        BigInteger.ZERO,
                        new LinkedHashSet<LLVMHeuristicVariable>(),
                        aborter
                    ) :
                        LLVMHeuristicRelation.computeBiggestKnownOffsetBetween(
                            state,
                            next,
                            other2,
                            sameSide,
                            BigInteger.ZERO,
                            new LinkedHashSet<LLVMHeuristicVariable>(),
                            aborter
                        );
            if (biggestOffsetFromOther2 != null) {
                if (biggestOffsetFromOther2.compareTo(BigInteger.ZERO) != 0) {
                    res.add(
                        termFactory.create(
                            ArithmeticOperationType.ADD,
                            other1,
                            termFactory.constant(greater ? biggestOffsetFromOther2 : biggestOffsetFromOther2.negate())
                        )
                    );
                } else {
                    res.add(other1);
                }
            }
            if (biggestOffsetFromOther1 != null || biggestOffsetFromOther2 != null) {
                return res;
            }
            if (exprLinear.y.compareTo(BigInteger.ZERO) < 0) {
                this.addAddWithOffset(
                    state,
                    next,
                    res,
                    exprLinear.y,
                    new Triple<LLVMHeuristicTerm, LLVMHeuristicTerm, LLVMHeuristicTerm>(sameSide, other1, other2),
                    relType,
                    true,
                    params,
                    aborter
                );
            } else if (exprLinear.y.compareTo(BigInteger.ZERO) > 0) {
                this.addAddWithOffset(
                    state,
                    next,
                    res,
                    exprLinear.y,
                    new Triple<LLVMHeuristicTerm, LLVMHeuristicTerm, LLVMHeuristicTerm>(sameSide, other1, other2),
                    relType,
                    false,
                    params,
                    aborter
                );
            } else {
                final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
                LLVMHeuristicIntegerState nextState = state.setRelations(next);
                if (
                    nextState.checkRelation(relationFactory.createRelation(relType, other1, sameSide), aborter).x
                ) {
                    if (
                        !strict
                        && nextState.checkRelation(
                            relationFactory.createRelation(relType.toStrict(), other1, sameSide),
                            aborter
                        ).x
                    ) {
                        res.add(
                            greater ?
                                termFactory.create(ArithmeticOperationType.ADD, other2, termFactory.one()) :
                                    termFactory.create(ArithmeticOperationType.SUB, other2, termFactory.one())
                        );
                    } else {
                        res.add(other2);
                    }
                }
                if (
                    nextState.checkRelation(relationFactory.createRelation(relType, other2, sameSide), aborter).x
                ) {
                    if (
                        !strict
                        && nextState.checkRelation(
                            relationFactory.createRelation(relType.toStrict(), other2, sameSide),
                            aborter
                        ).x
                    ) {
                        res.add(
                            greater ?
                                termFactory.create(ArithmeticOperationType.ADD, other1, termFactory.one()) :
                                    termFactory.create(ArithmeticOperationType.SUB, other1, termFactory.one())
                        );
                    } else {
                        res.add(other1);
                    }
                }
            }
            return res;
        }
        return Collections.<LLVMHeuristicTerm>emptySet();
    }

    /**
     * @param state The abstract state.
     * @param next The relations to consider for further inference.
     * @param res The set of expressions known to be in the desired relation to the original expression.
     * @param exprOffset The offset of the original expression.
     * @param exprs The expression on the same side of the complex relation as the original expression and the two
     *              expressions on the other side of that relation.
     * @param relType The relation type we are looking for.
     * @param negative Is exprOffset negative?
     * @param params Strategy parameters.
     */
    private void addAddWithOffset(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicRelationSet next,
        Set<LLVMHeuristicTerm> res,
        BigInteger exprOffset,
        Triple<LLVMHeuristicTerm, LLVMHeuristicTerm, LLVMHeuristicTerm> exprs,
        IntegerRelationType relType,
        boolean negative,
        LLVMParameters params,
        Abortion aborter
    ) {
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        LLVMHeuristicConstRef offset = termFactory.constant(negative ? exprOffset.negate() : exprOffset);
        Pair<Boolean, Boolean> flags = relType.toFlags();
        boolean strict = flags.x;
        boolean greater = flags.y;
        LLVMHeuristicTerm sameSide = exprs.x;
        LLVMHeuristicTerm other1 = exprs.y;
        LLVMHeuristicTerm other2 = exprs.z;
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> other1Linear = other1.toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> other2Linear = other2.toLinear();
        ArithmeticOperationType opType = negative ? ArithmeticOperationType.SUB : ArithmeticOperationType.ADD;
        LLVMHeuristicTerm otherSide1 =
            other1Linear.x == null ?
                termFactory.constant(other1Linear.y.add(exprOffset)) :
                    termFactory.create(opType, other1, offset);
        LLVMHeuristicTerm otherSide2 =
            other2Linear.x == null ?
                termFactory.constant(other2Linear.y.add(exprOffset)) :
                    termFactory.create(opType, other2, offset);
        LLVMHeuristicIntegerState nextState = state.setRelations(next);
        if (nextState.checkRelation(relationFactory.createRelation(relType, otherSide1, sameSide), aborter).x) {
            if (
                !strict
                && nextState.checkRelation(
                    relationFactory.createRelation(relType.toStrict(), otherSide1, sameSide),
                    aborter
                ).x
            ) {
                res.add(
                    greater ?
                        (other2Linear.x == null ?
                            termFactory.constant(other2Linear.y.add(BigInteger.ONE)) :
                                termFactory.create(
                                    ArithmeticOperationType.ADD,
                                    other2,
                                    termFactory.one()
                                )
                        ) :
                            (other2Linear.x == null ?
                                termFactory.constant(other2Linear.y.subtract(BigInteger.ONE)) :
                                    termFactory.create(
                                        ArithmeticOperationType.SUB,
                                        other2,
                                        termFactory.one()
                                    )
                            )
                );
            } else {
                res.add(other2);
            }
        }
        if (nextState.checkRelation(relationFactory.createRelation(relType, otherSide2, sameSide), aborter).x) {
            if (
                !strict
                && nextState.checkRelation(
                    relationFactory.createRelation(relType.toStrict(), otherSide2, sameSide),
                    aborter
                ).x
            ) {
                res.add(
                    greater ?
                        (other1Linear.x == null ?
                            termFactory.constant(other1Linear.y.add(BigInteger.ONE)) :
                                termFactory.create(
                                    ArithmeticOperationType.ADD,
                                    other1,
                                    termFactory.one()
                                )
                        ) :
                            (other1Linear.x == null ?
                                termFactory.constant(other1Linear.y.subtract(BigInteger.ONE)) :
                                    termFactory.create(
                                        ArithmeticOperationType.SUB,
                                        other1,
                                        termFactory.one()
                                    )
                            )
                );
            } else {
                res.add(other1);
            }
        }
    }

    /**
     * @param newLits The literal list to add a new literal to.
     * @param linear The new literal in linearized form.
     * @param divisor The divisor to apply to the literal.
     * @return True if we could add the literal. False if the division would not be precise on integers.
     */
    private boolean addLiteral(
        List<LLVMHeuristicTerm> newLits,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear,
        BigInteger divisor
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        if (linear.x == null) {
            if (linear.y.remainder(divisor).compareTo(BigInteger.ZERO) != 0) {
                // we won't succeed in precise division
                return false;
            }
            newLits.add(termFactory.constant(linear.y.divide(divisor)));
        } else {
            if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                assert (linear.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
            }
            if (linear.z.remainder(divisor).compareTo(BigInteger.ZERO) != 0) {
                // we won't succeed in precise division
                return false;
            }
            newLits.add(termFactory.create(linear.x, BigInteger.ZERO, linear.z.divide(divisor)));
        }
        return true;
    }

//    /**
//     * @return an SMTLIB atom corresponding to the encoded integer information.
//     */
//    public SMTLIBTheoryAtom toSMTAtom() {
//        SMTLIBIntValue leftValue = this.getLhs().toSMTIntValue();
//        SMTLIBIntValue rightValue = this.getRhs().toSMTIntValue();
//        if (leftValue == null || rightValue == null) {
//            return SMTLIBBoolTrue.create();
//        }
//        switch (this.type) {
//        case LT:
//            return SMTLIBIntLT.create(leftValue, rightValue);
//        case LE:
//            return SMTLIBIntLE.create(leftValue, rightValue);
//        case EQ:
//            return SMTLIBIntEquals.create(leftValue, rightValue);
//        case NE:
//            return SMTLIBIntUnequal.create(leftValue, rightValue);
//        default:
//            throw new IllegalStateException("Unknown relation type");
//        }
//    }

//    /**
//     * Creates a SMT-formula of the relation.
//     * @return The SMT-formula.
//     */
//    public Formula<SMTLIBTheoryAtom> toSMTFormula() {
//        return this.toSMTFormula(new AtomCachingFactory<SMTLIBTheoryAtom>());
//    }

//    /**
//     * Creates a SMT-formula of the relation.
//     * @param factory The formula factory.
//     * @return The SMT-formula.
//     */
//    public Formula<SMTLIBTheoryAtom> toSMTFormula(FormulaFactory<SMTLIBTheoryAtom> factory) {
//        return factory.buildTheoryAtom(this.toSMTAtom());
//    }

    /**
     * @param literals The literals to build the expression from.
     * @param index The index of the literal to replace.
     * @param literal The literal to set at the specified index.
     * @param offset A constant offset to add to the overall expression.
     * @return For literals x_1,...,x_index,...,x_n build an expression corresponding to the literals
     *         offset,x_1,...,sign literal,...,x_n.
     */
    private LLVMHeuristicTerm buildExpression(
        List<LLVMHeuristicTerm> literals,
        int index,
        LLVMHeuristicTerm literal,
        BigInteger offset
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        LLVMHeuristicTerm res = termFactory.constant(offset);
        for (int i = 0; i < literals.size(); i++) {
            if (i == index) {
                res = termFactory.create(ArithmeticOperationType.ADD, res, literal);
            } else {
                res = termFactory.create(ArithmeticOperationType.ADD, res, literals.get(i));
            }
        }
        return res;
    }

    /**
     * @param ref The reference to build the expression for.
     * @param litsOnOtherSide The literals on the other side of this relation than the one containing <code>ref</code>.
     * @param litsOnSameSide The literals on the same side of the relation as the one containing <code>ref</code>.
     * @param divisor A divisor by which all literals must be divided to obtain the expression.
     * @param indexOfRef The index of <code>ref</code> in <code>litsOnSameSide</code>.
     * @param refIsOnLeftSide Flag indicating whether <code>ref</code> is contained in the left-hand side of this
     *                        relation.
     * @return An expression known to be in relation to <code>ref</code> and a Boolean flag indicating the type of the
     *         relation (<code>null</code> means equality, <code>true</code> means the reference is greater than or
     *         equal to the expression, and <code>false</code> means the reference if less than or equal to the
     *         expression - the latter two possibilities are only considered if this relation is a directed inequality
     *         and nothing is "dropped" from this relation to compute the expression in relation to <code>ref</code>).
     */
    private Pair<LLVMHeuristicTerm, Boolean> buildExpression(
        LLVMHeuristicVariable ref,
        List<LLVMHeuristicTerm> litsOnOtherSide,
        List<LLVMHeuristicTerm> litsOnSameSide,
        BigInteger divisor,
        int indexOfRef,
        boolean refIsOnLeftSide
    ) {
        List<LLVMHeuristicTerm> newLits = new ArrayList<LLVMHeuristicTerm>();
        for (LLVMHeuristicTerm lit : litsOnOtherSide) {
            if (!this.addLiteral(newLits, lit.toLinear(), divisor)) {
                return null;
             }
        }
        int j = 0;
        for (LLVMHeuristicTerm lit : litsOnSameSide) {
            if (j == indexOfRef) {
                j++;
                continue;
            }
            if (!this.addLiteral(newLits, lit.negate().toLinear(), divisor)) {
               return null;
            }
            j++;
        }
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        LLVMHeuristicTerm res =
            (LLVMHeuristicTerm)
                ObjectUtils.binaryFold(
                    newLits,
                    termFactory.zero(),
                    ArithmeticOperationType.ADD,
                    new LLVMTermCombinator(termFactory)
                );
        boolean greater =
            refIsOnLeftSide ? divisor.compareTo(BigInteger.ZERO) < 0 : divisor.compareTo(BigInteger.ZERO) > 0;
        switch (this.getHeuristicRelationType()) {
            case EQ:
                return new Pair<LLVMHeuristicTerm, Boolean>(res, null);
            case LT:
                if (greater) {
                    res = termFactory.create(ArithmeticOperationType.ADD, termFactory.one(), res);
                } else {
                    res = termFactory.create(ArithmeticOperationType.ADD, termFactory.negone(), res);
                }
                // fall through
            case LE:
                return new Pair<LLVMHeuristicTerm, Boolean>(res, greater);
            default:
                throw new IllegalStateException("We should never reach this point!");
        }
    }

    /**
     * We have an equation of the form resRef = opLhs + opRhs.
     * @param state The abstract state holding the knowledge about the references.
     * @param expr An expression.
     * @param resRef A reference.
     * @param opLhs A reference.
     * @param opRhs A reference.
     * @param res A set of expressions known to be in the desired relation from expr.
     * @param strict Strict or weak relation?
     * @param greater Greater or less than relation?
     */
    private void handleAdditionEquation(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicTerm expr,
        LLVMHeuristicVariable resRef,
        LLVMHeuristicVariable opLhs,
        LLVMHeuristicVariable opRhs,
        Set<LLVMHeuristicTerm> res,
        boolean strict,
        boolean greater
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        if (resRef.equals(expr)) {
            if (
                !opLhs.isConcrete()
                && LLVMHeuristicIntegerState.isInRelationByAddition(
                    state.getValue(opRhs).getThisAsAbstractBoundedInt(),
                    strict,
                    greater
                )
            ) {
                res.add(opLhs);
            }
            if (
                !opRhs.isConcrete()
                && LLVMHeuristicIntegerState.isInRelationByAddition(
                    state.getValue(opLhs).getThisAsAbstractBoundedInt(),
                    strict,
                    greater
                )
            ) {
                res.add(opRhs);
            }
        } else if (resRef.isConcrete()) {
            return;
        }
        if (
            (
                // resRef = opLhs + opRhs <=> opLhs = resRef - opRhs
                opLhs.equals(expr)
                && LLVMHeuristicIntegerState.isInRelationBySubtraction(
                    state.getValue(opRhs).getThisAsAbstractBoundedInt(),
                    strict,
                    greater
                )
            )
            || (
                // resRef = opLhs + opRhs <=> opRhs = resRef - opLhs
                opRhs.equals(expr)
                && LLVMHeuristicIntegerState.isInRelationBySubtraction(
                    state.getValue(opLhs).getThisAsAbstractBoundedInt(),
                    strict,
                    greater
                )
            )
        ) {
            res.add(resRef);
        } else if (!strict) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
            if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                assert (exprLinear.x != null) : "This should have been caught before calling this method!";
            }
            if (
                exprLinear.y.compareTo(BigInteger.ZERO) == 0
                || exprLinear.z.compareTo(BigInteger.ONE) != 0
                || !(exprLinear.x instanceof LLVMHeuristicOperation)
            ) {
                return;
            }
            LLVMHeuristicOperation exprOp = (LLVMHeuristicOperation)exprLinear.x;
            if (!exprOp.isSimple()) {
                return;
            }
            LLVMHeuristicVariable ref1 = (LLVMHeuristicVariable)exprOp.getLhs();
            LLVMHeuristicVariable ref2 = (LLVMHeuristicVariable)exprOp.getRhs();
            LLVMHeuristicVariable opRef;
            BigInteger offset;
            if (opLhs instanceof LLVMHeuristicConstRef && opRhs instanceof LLVMHeuristicVarRef) {
                opRef = opRhs;
                offset = ((LLVMHeuristicConstRef)opLhs).getIntegerValue();
            } else if (opLhs instanceof LLVMHeuristicVarRef && opRhs instanceof LLVMHeuristicConstRef) {
                opRef = opLhs;
                offset = ((LLVMHeuristicConstRef)opRhs).getIntegerValue();
            } else {
                opRef = null;
                offset = null;
            }
            if (opRef == null || offset.compareTo(exprLinear.y) != 0) {
                return;
            }
            if (ref1.equals(opRef)) {
                res.add(termFactory.create(exprOp.getOperation(), ref2, resRef));
            } else if (ref2.equals(opRef)) {
                res.add(termFactory.create(exprOp.getOperation(), ref1, resRef));
            }
        }
    }

    /**
     * @param state The state holding the knowledge about the references.
     * @param knownRels The relations to consider.
     * @param expr An expression.
     * @param res The set of expressions known to be in the desired relation from expr.
     * @param strict Strict relation?
     * @param greater Greater or less than?
     * @param params Strategy parameters.
     */
    private void handleComplexRelation(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicRelationSet knownRels,
        LLVMHeuristicTerm expr,
        Set<LLVMHeuristicTerm> res,
        boolean strict,
        boolean greater,
        LLVMParameters params,
        Abortion aborter
    ) {
        LLVMHeuristicOperation lhsOp = (LLVMHeuristicOperation)this.getLhs();
        LLVMHeuristicOperation rhsOp = (LLVMHeuristicOperation)this.getRhs();
        if (
            (!greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ)
            && lhsOp.equals(expr)
            && rhsOp.isSimple()
        ) {
            res.addAll(
                LLVMHeuristicRelation.handleExpressionEquation(
                    state,
                    rhsOp.getOperation(),
                    (LLVMHeuristicVariable)rhsOp.getLhs(),
                    (LLVMHeuristicVariable)rhsOp.getRhs(),
                    strict,
                    greater
                )
            );
        } else if (
            (greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ)
            && rhsOp.equals(expr)
            && lhsOp.isSimple()
        ) {
            res.addAll(
                LLVMHeuristicRelation.handleExpressionEquation(
                    state,
                    lhsOp.getOperation(),
                    (LLVMHeuristicVariable)lhsOp.getLhs(),
                    (LLVMHeuristicVariable)lhsOp.getRhs(),
                    strict,
                    greater
                )
            );
        }
        if (!lhsOp.isSimple() || !rhsOp.isSimple()) {
            // this is too complex for us (by now)
            return;
        }
        LLVMHeuristicVariable left1 = (LLVMHeuristicVariable)lhsOp.getLhs();
        LLVMHeuristicVariable left2 = (LLVMHeuristicVariable)lhsOp.getRhs();
        LLVMHeuristicVariable right1 = (LLVMHeuristicVariable)rhsOp.getLhs();
        LLVMHeuristicVariable right2 = (LLVMHeuristicVariable)rhsOp.getRhs();
        if (
            left1 instanceof LLVMHeuristicConstRef
            || left2 instanceof LLVMHeuristicConstRef
            || right1 instanceof LLVMHeuristicConstRef
            || right2 instanceof LLVMHeuristicConstRef
        ) {
            // don't do this for constants
            return;
        }
        switch (lhsOp.getOperation()) {
            case ADD:
                switch (rhsOp.getOperation()) {
                    case ADD:
                        res.addAll(
                            this.addAddPattern(
                                state,
                                knownRels,
                                expr,
                                new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(left1, left2),
                                new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(right1, right2),
                                strict,
                                greater,
                                params,
                                aborter
                            )
                        );
                        break;
                    case SUB:
                        if (
                            (!greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ)
                            && LLVMHeuristicRelation.addSubPattern(state, expr, left1, left2, right2, strict, greater)
                        ) {
                            res.add(right1);
                        }
                        break;
                    default:
                        // too complicated (for now)
                }
                break;
            case SUB:
                switch (rhsOp.getOperation()) {
                    case ADD:
                        if (
                            (greater || this.getHeuristicRelationType() == LLVMHeuristicRelationType.EQ)
                            && LLVMHeuristicRelation.addSubPattern(state, expr, right1, right2, left2, strict, greater)
                        ) {
                            res.add(left1);
                        }
                        break;
                    case SUB:
                        // left1 - left2 =/<=/< right1 - right2 <=> left1 + right2 =/<=/< right1 + left2
                        res.addAll(
                            this.addAddPattern(
                                state,
                                knownRels,
                                expr,
                                new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(left1, right2),
                                new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(right1, left2),
                                strict,
                                greater,
                                params,
                                aborter
                            )
                        );
                        break;
                    default:
                        // too complicated (for now)
                }
                break;
            default:
                // too complicated (for now)
        }
    }

    /**
     * @param state The state holding the knowledge about the references.
     * @param expr An expression.
     * @param res The set of expressions known to be in the desired relation from expr.
     * @param strict Strict relation?
     * @param greater Greater or less than?
     */
    private void handleEquationWithValues(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicTerm expr,
        Set<LLVMHeuristicTerm> res,
        boolean strict,
        boolean greater
    ) {
        LLVMHeuristicVariable resRef;
        LLVMHeuristicOperation op;
        if (this.getLhs() instanceof LLVMHeuristicVariable && this.getRhs() instanceof LLVMHeuristicOperation) {
            resRef = (LLVMHeuristicVariable)this.getLhs();
            op = (LLVMHeuristicOperation) this.getRhs();
        } else if (this.getRhs() instanceof LLVMHeuristicVariable && this.getLhs() instanceof LLVMHeuristicOperation) {
            resRef = (LLVMHeuristicVariable)this.getRhs();
            op = (LLVMHeuristicOperation)this.getLhs();
        } else {
            resRef = null;
            op = null;
        }
        if (resRef == null || !op.isSimple()) {
            return;
        }
        LLVMHeuristicVariable opLhs = (LLVMHeuristicVariable)op.getLhs();
        LLVMHeuristicVariable opRhs = (LLVMHeuristicVariable)op.getRhs();
        // we have a relation of the form resRef = opLhs op.getOpType() opRhs
        if (opLhs instanceof LLVMHeuristicVarRef && opRhs instanceof LLVMHeuristicVarRef) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> exprLinear = expr.toLinear();
            if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                assert (exprLinear.x != null) : "Tried to find related expressions for a constant... Why?!";
            }
            if (exprLinear.z.compareTo(BigInteger.ONE) == 0) {
                /*
                 * we have:
                 * expr = x + c1
                 * z = x + y
                 * we want:
                 * x + c1 > z
                 * find:
                 * x + c2 such that x + y <= x + c2 and c1 > c2
                 * then:
                 * x + c1 > x + c2 >= x + y = z
                 */
                for (
                    LLVMHeuristicTerm bridge :
                        LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(
                            op,
                            state.getValues(),
                            false,
                            !greater
                        )
                ) {
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> bridgeLinear = bridge.toLinear();
                    if (
                        !exprLinear.x.equals(bridgeLinear.x)
                        || bridgeLinear.z.compareTo(BigInteger.ONE) != 0
                        || !LLVMHeuristicIntegerState.isInRelation(exprLinear.y, bridgeLinear.y, strict, greater)
                    ) {
                        continue;
                    }
                    res.add(resRef);
                    break;
                }
            }
        }
        switch (op.getOperation()) {
            case ADD:
                this.handleAdditionEquation(state, expr, resRef, opLhs, opRhs, res, strict, greater);
                break;
            case SUB:
                // resRef = opLhs - opRhs <=> opLhs = resRef + opRhs
                this.handleAdditionEquation(state, expr, opLhs, resRef, opRhs, res, strict, greater);
                break;
            default:
                // do nothing
        }
    }

}
