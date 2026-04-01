package aprove.input.Programs.llvm.internalStructures.expressions.relations;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Represent a set (conjunction) of relations between variables. This set must not contain null.
 * @author Janine Repke, Peter Schneider-Kamp, cryingshadow
 */
public class LLVMHeuristicRelationSet implements Set<LLVMHeuristicRelation>, Substitutable, SMTSExpressible<SBool> {

    /**
     * Time used to construct formulas. Used for debugging/profiling.
     */
    public static long formulaConstruction = 0;

    /**
     * Number of SMT calls. Used for debugging/profiling.
     */
    public static int smtCalls = 0;

    /**
     * Time used for SMT solving. Used for debugging/profiling.
     */
    public static long smtSolving = 0;

    /**
     * @param offset A new constant offset.
     * @param factor A new constant factor
     * @param old The former match holding the old offset and factor in its second and third component.
     * @return True if the new offset/factor pair is better than the old one. Better means that we prefer positive
     *         factors over smaller factors over positive offsets over smaller offsets over anything else. False
     *         otherwise.
     */
    private static boolean betterMatch(
        BigInteger offset,
        BigInteger factor,
        Triple<LLVMHeuristicVariable, BigInteger, BigInteger> old
    ) {
        return
            (old.z.compareTo(BigInteger.ZERO) < 0 && factor.compareTo(BigInteger.ZERO) > 0)
            || (
                old.z.signum() == factor.signum()
                && (
                    old.z.abs().compareTo(factor.abs()) > 0
                    || (
                        old.z.compareTo(factor) == 0
                        && (
                            (old.y.compareTo(BigInteger.ZERO) < 0 && offset.compareTo(BigInteger.ZERO) > 0)
                            || (
                                old.y.signum() == offset.signum()
                                && old.y.abs().compareTo(offset.abs()) > 0
                            )
                        )
                    )
                )
            );
    }

//    /**
//     * @param valueMap The values for the references.
//     * @return an SMT expression that encodes all information about integer values known in <code>state</code>
//     */
//    private static SMTExpression<SBool> integerBoundInformationToSMTExp(
//        ImmutableMap<LLVMHeuristicVariable, LLVMValue> valueMap
//    ) {
//        List<SMTExpression<SBool>> subformulas = new LinkedList<>();
//        for (Map.Entry<LLVMHeuristicVariable, LLVMValue> e : valueMap.entrySet()) {
//            LLVMHeuristicVariable ref = e.getKey();
//            AbstractBoundedInt value = e.getValue().getThisAsAbstractBoundedInt();
//            SMTExpression<SInt> refExp = ref.toSMTExp();
//            if (value instanceof LiteralBoundedInt) {
//                subformulas.add(Core.equivalent(refExp, ((LiteralBoundedInt) value).toSMTExp()));
//            } else if (value instanceof IntervalBoundedInt) {
//                AbstractBoundedInt absIntValue = value;
//                IntervalBound lowBound = absIntValue.getLower();
//                if (lowBound.isFinite()) {
//                    subformulas.add(Ints.greaterEqual(refExp, Ints.constant(lowBound.getConstant())));
//                }
//                IntervalBound upperBound = absIntValue.getUpper();
//                if (upperBound.isFinite()) {
//                    subformulas.add(Ints.lessEqual(refExp, Ints.constant(upperBound.getConstant())));
//                }
//                // IntervalInts are not "just" intervals of integers,
//                // the number 0 has a special treatment
//                if (
//                    !absIntValue.containsLiteral(BigInteger.ZERO)
//                    && lowBound.isNegative()
//                    && upperBound.isPositive()
//                ) {
//                    subformulas.add(Core.not(Core.equivalent(refExp, Ints.constant(0))));
//                }
//            }
//        }
//        return Core.and(subformulas);
//    }

    /**
     * The set containing the relations;
     */
    private IntegerRelationSet set;

    /**
     * Creates an empty set.
     */
    public LLVMHeuristicRelationSet() {
        this.set = new IntegerRelationSet();
    }

    /**
     * Creates a set of equalities
     * @param equalities
     *        Each entry in equalities is treated as an equation and added to
     *        the new RelationSet
     */
    public LLVMHeuristicRelationSet(
        Map<? extends LLVMHeuristicTerm, ? extends LLVMHeuristicTerm> equalities
    ) {
        this();
        for (
            Map.Entry<? extends LLVMHeuristicTerm, ? extends LLVMHeuristicTerm> equality : equalities.entrySet()
        ) {
            this.add(
                LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY.createRelation(
                    LLVMHeuristicRelationType.EQ,
                    equality.getKey(),
                    equality.getValue()
                )
            );
        }
    }

    /**
     * Creates a set containing all elements in the specified set.
     * @param set The set containing the elements (must not contain null).
     */
    public LLVMHeuristicRelationSet(Set<? extends LLVMHeuristicRelation> set) {
        this();
        this.addAll(set);
    }

    /**
     * @param eqs The equations.
     * @param ineqs The undirected inequalities.
     * @param strict The strict directed inequalities.
     * @param weak The weak directed inequalities.
     */
    private LLVMHeuristicRelationSet(
        Set<IntegerRelation> eqs,
        Set<IntegerRelation> ineqs,
        Set<IntegerRelation> strict,
        Set<IntegerRelation> weak
    ) {
        this.set = new IntegerRelationSet(eqs, ineqs, strict, weak);
    }

    @Override
    public boolean add(LLVMHeuristicRelation rel) {
        return this.set.add(rel);
    }

    @Override
    public boolean addAll(Collection<? extends LLVMHeuristicRelation> c) {
        return this.set.addAll(c);
    }

    /**
     * Adds the relation to the relation set. If the relation is already implied by the other relations, it is not
     * added. If we already have a similar relation (the expressions on both sides match) which is weaker, the weaker
     * relation is dropped. If the negation of the relation is implied by the other relations, an IllegalStateException
     * is thrown.
     * @param state The abstract state holding knowledge about the references.
     * @param rel The relation to add (must not be null).
     * @param useCache Should we use the cache?
     * @param aborter For abortions.
     * @return True if the specified relation is really added. False if it was already implied.
     */
    public Pair<Boolean, ? extends LLVMHeuristicIntegerState> addRelation(
        LLVMHeuristicIntegerState state,
        LLVMHeuristicRelation rel,
        boolean useCache,
        Abortion aborter
    ) {
        // check if new relation is a tautology, stronger than an old one, or weaker than an old one
        LLVMHeuristicTerm lhs = rel.getLhs();
        LLVMHeuristicTerm rhs = rel.getRhs();
        IntegerRelationType newCC = rel.getRelationType();
        Pair<Boolean, ? extends LLVMHeuristicIntegerState> check = state.checkRelation(rel, aborter);
        LLVMHeuristicIntegerState newState = check.y;
        if (check.x) {
            // we knew this already
            check.x = false;
            return check;
        }
        check = newState.checkRelation(rel.negate(), aborter);
        newState = check.y;
        if (check.x) {
            throw new InconsistentStateException(state, rel);
        }
        Iterator<LLVMHeuristicRelation> itr = this.iterator();
        final LLVMHeuristicRelationFactory factory = LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY;
        while (itr.hasNext()) {
            LLVMHeuristicRelation curRel = itr.next();
            LLVMHeuristicTerm curLhs = curRel.getLhs();
            LLVMHeuristicTerm curRhs = curRel.getRhs();
            if (curLhs.equals(lhs) && curRhs.equals(rhs)) {
                // if a relation of the same type is found, no other relations of the type are in the set
                // => stop looking for other relations (all branches lead to return statements)
                IntegerRelationType relType = curRel.getRelationType();
                if (
                    (relType == IntegerRelationType.NE && newCC == IntegerRelationType.LE)
                    || (relType == IntegerRelationType.LE && newCC == IntegerRelationType.NE)
                ) {
                    // this is an incomparable case w.r.t. subsumption and it leads to an LT relation
                    itr.remove();
                    return
                        new Pair<Boolean, LLVMHeuristicIntegerState>(
                            this.add(factory.createRelation(LLVMHeuristicRelationType.LT, lhs, rhs)),
                            newState
                        );
                }
                if (newCC.subSumes(relType)) {
                    // the new relation is stronger
                    // => remove the old relation and add the new relation to the set
                    itr.remove();
                    return new Pair<Boolean, LLVMHeuristicIntegerState>(this.add(rel), newState);
                }
                if (Globals.useAssertions) {
                    assert (relType.subSumes(newCC)) : "Tried to add a contradictive relation!";
                }
                // old relation is stronger or the same
                // => old relation can stay in the set
                return new Pair<Boolean, LLVMHeuristicIntegerState>(false, newState);
            } else if (curLhs.equals(rhs) && curRhs.equals(lhs)) {
                // if a relation of the same type is found, no other relations of the type are in the set
                // => stop looking for other relations (all branches lead to return statements)
                IntegerRelationType relType = curRel.getRelationType();
                if (relType == IntegerRelationType.NE && newCC == IntegerRelationType.LE) {
                    // this is an incomparable case w.r.t. subsumption and it leads to an LT relation
                    // note that we need to take the arguments for the LT relation from rel
                    itr.remove();
                    return
                        new Pair<Boolean, LLVMHeuristicIntegerState>(
                            this.add(factory.createRelation(LLVMHeuristicRelationType.LT, lhs, rhs)),
                            newState
                        );
                }
                if (relType == IntegerRelationType.LE && newCC == IntegerRelationType.NE) {
                    // this is an incomparable case w.r.t. subsumption and it leads to an LT relation
                    // note that we need to take the arguments for the LT relation from actRel
                    itr.remove();
                    return
                        new Pair<Boolean, LLVMHeuristicIntegerState>(
                            this.add(factory.createRelation(LLVMHeuristicRelationType.LT, curLhs, curRhs)),
                            newState
                        );
                }
                if (relType == IntegerRelationType.LE && newCC == IntegerRelationType.LE) {
                    throw new IllegalStateException(
                        "Adding two weak inequalities would result in an equation - "
                        + "but this should have been detected earlier!"
                    );
                }
                IntegerRelationType mirrorType = relType.mirror();
                if (newCC.subSumes(mirrorType)) {
                    // the new relation is stronger
                    // => remove the old relation and add the new relation to the set
                    itr.remove();
                    return new Pair<Boolean, LLVMHeuristicIntegerState>(this.add(rel), newState);
                }
                if (Globals.useAssertions) {
                    assert (mirrorType.subSumes(newCC)) : "Tried to add a contradictive relation!";
                }
                // old relation is stronger or the same
                // => old relation can stay in the set
                return new Pair<Boolean, LLVMHeuristicIntegerState>(false, newState);
            }
        }
        return new Pair<Boolean, LLVMHeuristicIntegerState>(this.add(rel), newState);
    }

    /**
     * Adds all given relations to the set if they are not already implied.
     * @param state The abstract state holding the knowledge about the references.
     * @param newRelations The relations to add (must not contain null).
     * @param useCache Should we use the cache?
     * @param aborter For abortions.
     * @return The set of really added relations.
     */
    public LLVMHeuristicRelationSet addRelations(
        LLVMHeuristicIntegerState state,
        Collection<? extends LLVMHeuristicRelation> newRelations,
        boolean useCache,
        Abortion aborter
    ) {
        LLVMHeuristicRelationSet res = new LLVMHeuristicRelationSet();
        // TODO can we use the updates here?
        for (LLVMHeuristicRelation rel : newRelations) {
            if (this.addRelation(state.setRelations(this), rel, useCache, aborter).x) {
                res.add(rel);
            }
        }
        return res;
    }

    /**
     * Apply the substitution to all relations within this set. Attention: This might yield tautological relations
     * which must be cleaned thereafter!
     * @param sigma The substitution.
     */
    @Override
    public LLVMHeuristicRelationSet applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        this.set.applySubstitution(sigma);
        return this;
    }

    /**
     * Apply the substitution to all relations within this set. Attention: This might yield tautological relations
     * which must be cleaned thereafter!
     * @param sigma The substitution.
     */
    @Override
    public LLVMHeuristicRelationSet applySubstitution(Substitution sigma) {
        this.set.applySubstitution(sigma);
        return this;
    }

    @Override
    public void clear() {
        this.set.clear();
    }

    /**
     * Removes all equations from this relation set.
     */
    public void clearEquations() {
        this.set.clearEquations();
    }

    /**
     * Removes all weak directed inequalities from this RelationSet.
     */
    public void clearWeakDirectedInequalities() {
        this.set.clearWeakDirectedInequalities();
    }

    /**
     * @return The highest absolute multiplicative constant factor occurring in one of these relations.
     */
    public BigInteger computeHighestAbsoluteFactor() {
        BigInteger res = BigInteger.ONE;
        for (LLVMHeuristicRelation rel : this) {
            res = res.max(rel.computeHighestAbsoluteFactor());
        }
        return res;
    }

    /**
     * @return A set of all non-reference expressions occurring in one of these relations.
     */
    public Set<LLVMHeuristicTerm> computeInterestingExpressions() {
        Set<LLVMHeuristicTerm> res = new LinkedHashSet<LLVMHeuristicTerm>();
        for (LLVMHeuristicRelation rel : this) {
            for (LLVMHeuristicTerm expr : rel.getLhs().computeAllSubExpressions()) {
                if (!(expr instanceof LLVMHeuristicVariable)) {
                    res.add(expr);
                }
            }
            for (LLVMHeuristicTerm expr : rel.getRhs().computeAllSubExpressions()) {
                if (!(expr instanceof LLVMHeuristicVariable)) {
                    res.add(expr);
                }
            }
        }
        return res;
    }

    /**
     * @return The maximal number of positions holding a variable within a relation from this set.
     */
    public int computeMaximalNumberOfVariableOccurrences() {
        int res = 0;
        for (LLVMHeuristicRelation rel : this) {
            res = Math.max(res, rel.getNumberOfVarOccs());
        }
        return res;
    }

    @Override
    public boolean contains(Object o) {
        return this.set.contains(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return this.set.containsAll(c);
    }

    /**
     * @param firstRef Some reference.
     * @param secondRef Some other reference.
     * @return True if this relation set contains equations with both references and some multiplicative term and
     *         between the references such that we can deduce that they are in different remainder classes. False
     *         otherwise.
     */
    public boolean differentRemainderClasses(LLVMHeuristicVariable firstRef, LLVMHeuristicVariable secondRef) {
        // maps refs to sets of pairs (a,b) with a > 1 and meaning ref % a = b
        Map<LLVMHeuristicVariable, Set<Pair<BigInteger, BigInteger>>> remainderClasses =
            new LinkedHashMap<LLVMHeuristicVariable, Set<Pair<BigInteger, BigInteger>>>();
        for (LLVMHeuristicRelation rel : this.getEquations()) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
            // multiplication cases
            if (
                lhsLinear.x instanceof LLVMHeuristicVariable
                && lhsLinear.z.compareTo(BigInteger.ONE) == 0
                && rhsLinear.x != null
                && rhsLinear.y.subtract(lhsLinear.y).compareTo(BigInteger.ZERO) == 0
            ) {
                if (rhsLinear.z.abs().compareTo(BigInteger.ONE) > 0) {
                    LLVMHeuristicVariable ref = (LLVMHeuristicVariable)lhsLinear.x;
                    if (!remainderClasses.containsKey(ref)) {
                        remainderClasses.put(ref, new LinkedHashSet<Pair<BigInteger, BigInteger>>());
                    }
                    remainderClasses.get(ref).add(new Pair<BigInteger, BigInteger>(rhsLinear.z.abs(), BigInteger.ZERO));
                }
            }
            if (
                rhsLinear.x instanceof LLVMHeuristicVariable
                && rhsLinear.z.compareTo(BigInteger.ONE) == 0
                && lhsLinear.x != null
                && lhsLinear.y.subtract(rhsLinear.y).compareTo(BigInteger.ZERO) == 0
            ) {
                if (lhsLinear.z.abs().compareTo(BigInteger.ONE) > 0) {
                    LLVMHeuristicVariable ref = (LLVMHeuristicVariable)rhsLinear.x;
                    if (!remainderClasses.containsKey(ref)) {
                        remainderClasses.put(ref, new LinkedHashSet<Pair<BigInteger, BigInteger>>());
                    }
                    remainderClasses.get(ref).add(new Pair<BigInteger, BigInteger>(lhsLinear.z.abs(), BigInteger.ZERO));
                }
            }
            // remainder cases
            if (lhsLinear.x == null && rhsLinear.x instanceof LLVMHeuristicOperation) {
                BigInteger remRes = lhsLinear.y.subtract(rhsLinear.y);
                if (remRes.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) == 0) {
                    remRes = remRes.divide(rhsLinear.z);
                    LLVMHeuristicOperation op = (LLVMHeuristicOperation)rhsLinear.x;
                    LLVMHeuristicTerm opLhs = op.getLhs();
                    LLVMHeuristicTerm opRhs = op.getRhs();
                    if (
                        op.getOperation() == ArithmeticOperationType.TMOD
                        && opRhs instanceof LLVMHeuristicConstRef
                        && opLhs instanceof LLVMHeuristicVarRef
                    ) {
                        LLVMHeuristicVariable ref = (LLVMHeuristicVariable)opLhs;
                        if (!remainderClasses.containsKey(ref)) {
                            remainderClasses.put(ref, new LinkedHashSet<Pair<BigInteger, BigInteger>>());
                        }
                        remainderClasses.get(
                            ref
                        ).add(
                            new Pair<BigInteger, BigInteger>(
                                ((LLVMHeuristicConstRef)opRhs).getIntegerValue().abs(),
                                remRes
                            )
                        );
                    }
                }
            } else if (rhsLinear.x == null && lhsLinear.x instanceof LLVMHeuristicOperation) {
                BigInteger remRes = rhsLinear.y.subtract(lhsLinear.y);
                if (remRes.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) == 0) {
                    remRes = remRes.divide(lhsLinear.z);
                    LLVMHeuristicOperation op = (LLVMHeuristicOperation)lhsLinear.x;
                    LLVMHeuristicTerm opLhs = op.getLhs();
                    LLVMHeuristicTerm opRhs = op.getRhs();
                    if (
                        op.getOperation() == ArithmeticOperationType.TMOD
                        && opRhs instanceof LLVMHeuristicConstRef
                        && opLhs instanceof LLVMHeuristicVarRef
                    ) {
                        LLVMHeuristicVariable ref = (LLVMHeuristicVariable)opLhs;
                        if (!remainderClasses.containsKey(ref)) {
                            remainderClasses.put(ref, new LinkedHashSet<Pair<BigInteger, BigInteger>>());
                        }
                        remainderClasses.get(
                            ref
                        ).add(
                            new Pair<BigInteger, BigInteger>(
                                ((LLVMHeuristicConstRef)opRhs).getIntegerValue().abs(),
                                remRes
                            )
                        );
                    }
                }
            }
        }
        if (remainderClasses.isEmpty()) {
            return false;
        }
        Map<LLVMHeuristicVariable, BigInteger> offsetsFirst = new LinkedHashMap<LLVMHeuristicVariable, BigInteger>();
        offsetsFirst.put(firstRef, BigInteger.ZERO);
        Map<LLVMHeuristicVariable, BigInteger> offsetsSecond = new LinkedHashMap<LLVMHeuristicVariable, BigInteger>();
        offsetsSecond.put(secondRef, BigInteger.ZERO);
        boolean changed = true;
        while (changed) {
            changed = false;
            for (LLVMHeuristicRelation rel : this.getEquations()) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
                Set<LLVMHeuristicVariable> alreadyFirst =
                    new LinkedHashSet<LLVMHeuristicVariable>(offsetsFirst.keySet());
                for (LLVMHeuristicVariable ref : alreadyFirst) {
                    if (ref.equals(lhsLinear.x)) {
                        if (
                            !offsetsFirst.containsKey(rhsLinear.x)
                            && rhsLinear.x instanceof LLVMHeuristicVariable
                            && lhsLinear.z.compareTo(rhsLinear.z) == 0
                        ) {
                            offsetsFirst.put(
                                (LLVMHeuristicVariable)rhsLinear.x,
                                rhsLinear.y.subtract(lhsLinear.y).add(offsetsFirst.get(ref))
                            );
                            changed = true;
                        }
                    } else if (ref.equals(rhsLinear.x)) {
                        if (
                            !offsetsFirst.containsKey(lhsLinear.x)
                            && lhsLinear.x instanceof LLVMHeuristicVariable
                            && rhsLinear.z.compareTo(lhsLinear.z) == 0
                        ) {
                            offsetsFirst.put(
                                (LLVMHeuristicVariable)lhsLinear.x,
                                lhsLinear.y.subtract(rhsLinear.y).add(offsetsFirst.get(ref))
                            );
                            changed = true;
                        }
                    }
                }
                Set<LLVMHeuristicVariable> alreadySecond =
                    new LinkedHashSet<LLVMHeuristicVariable>(offsetsSecond.keySet());
                for (LLVMHeuristicVariable ref : alreadySecond) {
                    if (ref.equals(lhsLinear.x)) {
                        if (
                            !offsetsSecond.containsKey(rhsLinear.x)
                            && rhsLinear.x instanceof LLVMHeuristicVariable
                            && lhsLinear.z.compareTo(rhsLinear.z) == 0
                        ) {
                            offsetsSecond.put(
                                (LLVMHeuristicVariable)rhsLinear.x,
                                rhsLinear.y.subtract(lhsLinear.y).add(offsetsSecond.get(ref))
                            );
                            changed = true;
                        }
                    } else if (ref.equals(rhsLinear.x)) {
                        if (
                            !offsetsSecond.containsKey(lhsLinear.x)
                            && lhsLinear.x instanceof LLVMHeuristicVariable
                            && rhsLinear.z.compareTo(lhsLinear.z) == 0
                        ) {
                            offsetsSecond.put(
                                (LLVMHeuristicVariable)lhsLinear.x,
                                lhsLinear.y.subtract(rhsLinear.y).add(offsetsSecond.get(ref))
                            );
                            changed = true;
                        }
                    }
                }
            }
        }
        offsetsFirst.keySet().retainAll(remainderClasses.keySet());
        offsetsSecond.keySet().retainAll(remainderClasses.keySet());
        for (Map.Entry<LLVMHeuristicVariable, BigInteger> entryFirst : offsetsFirst.entrySet()) {
            for (Map.Entry<LLVMHeuristicVariable, BigInteger> entrySecond : offsetsSecond.entrySet()) {
                for (Pair<BigInteger, BigInteger> firstPair : remainderClasses.get(entryFirst.getKey())) {
                    for (Pair<BigInteger, BigInteger> secondPair : remainderClasses.get(entrySecond.getKey())) {
                        if (firstPair.x.compareTo(secondPair.x) != 0) {
                            continue;
                        }
                        BigInteger firstVal = firstPair.y.add(entryFirst.getValue());
                        while (firstVal.compareTo(BigInteger.ZERO) < 0) {
                            firstVal = firstVal.add(firstPair.x);
                        }
                        BigInteger secondVal = secondPair.y.add(entrySecond.getValue());
                        while (secondVal.compareTo(BigInteger.ZERO) < 0) {
                            secondVal = secondVal.add(firstPair.x);
                        }
                        if (firstVal.compareTo(secondVal) != 0) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || !(o instanceof Set<?>)) {
            return false;
        }
        Set<?> other = (Set<?>)o;
        return this.containsAll(other) && other.containsAll(this);
    }

    /**
     * @return A set containing all directed (weak and strict) inequalities in this RelationSet.
     */
    public Set<LLVMHeuristicRelation> getDirectedInequalities() {
        Set<LLVMHeuristicRelation> res = new LinkedHashSet<LLVMHeuristicRelation>();
        for (IntegerRelation rel : this.set.getStrictDirectedInequalities()) {
            res.add((LLVMHeuristicRelation)rel);
        }
        for (IntegerRelation rel : this.set.getWeakDirectedInequalities()) {
            res.add((LLVMHeuristicRelation)rel);
        }
        return res;
    }

    /**
     * @return The equations in this relation set.
     */
    public Set<LLVMHeuristicRelation> getEquations() {
        Set<LLVMHeuristicRelation> res = new LinkedHashSet<LLVMHeuristicRelation>();
        for (IntegerRelation rel : this.set.getEquations()) {
            res.add((LLVMHeuristicRelation)rel);
        }
        return res;
    }

    /**
     * The order of lhs and rhs is irrelevant since getRelation(lhs, rhs) == getRelation(rhs, lhs).mirror().
     * @param lhs An expression.
     * @param rhs Another expression.
     * @return The relation the two expressions are in, if such a relation is part of the set. Null if no relation can
     *         be found.
     */
    public IntegerRelationType getRelation(LLVMHeuristicTerm lhs, LLVMHeuristicTerm rhs) {
        for (LLVMHeuristicRelation relation : this) {
            final LLVMHeuristicTerm currentLhs = relation.getLhs();
            final LLVMHeuristicTerm currentRhs = relation.getRhs();
            if (currentLhs.equals(lhs) && currentRhs.equals(rhs)) {
                return relation.getRelationType();
            } else if (currentRhs.equals(lhs) && currentLhs.equals(rhs)) {
                return relation.getRelationType().mirror();
            }
        }
        return null;
    }

    /**
     * @return This relation set without undirected inequalities.
     */
    public LLVMHeuristicRelationSet getRelationsWithoutUndirectedInequalities() {
        return
            new LLVMHeuristicRelationSet(
                this.set.getEquations(),
                Collections.<IntegerRelation>emptySet(),
                this.set.getStrictDirectedInequalities(),
                this.set.getWeakDirectedInequalities()
            );
    }

    /**
     * @return The inequalities lhs < rhs in this relation set.
     */
    public Set<LLVMHeuristicRelation> getStrictDirectedInequalities() {
        Set<LLVMHeuristicRelation> res = new LinkedHashSet<LLVMHeuristicRelation>();
        for (IntegerRelation rel : this.set.getStrictDirectedInequalities()) {
            res.add((LLVMHeuristicRelation)rel);
        }
        return res;
    }

    /**
     * @return The inequalities lhs != rhs in this relation set.
     */
    public Set<LLVMHeuristicRelation> getUndirectedInequalities() {
        Set<LLVMHeuristicRelation> res = new LinkedHashSet<LLVMHeuristicRelation>();
        for (IntegerRelation rel : this.set.getUndirectedInequalities()) {
            res.add((LLVMHeuristicRelation)rel);
        }
        return res;
    }

    /**
     * @return The inequalities lhs <= rhs in this relation set.
     */
    public Set<LLVMHeuristicRelation> getWeakDirectedInequalities() {
        Set<LLVMHeuristicRelation> res = new LinkedHashSet<LLVMHeuristicRelation>();
        for (IntegerRelation rel : this.set.getWeakDirectedInequalities()) {
            res.add((LLVMHeuristicRelation)rel);
        }
        return res;
    }

    @Override
    public int hashCode() {
        return this.set.hashCode() + 7;
    }

//    /**
//     * Deletes relations which are redundant. To determine this an SMT-Solver
//     * is used. This method is very expensive and should not be called very
//     * often.
//     * @throws AbortionException If solver is aborted.
//     */
//    public void reduceRelations() throws AbortionException {
//        // TODO this method is never used - keep it in case we need it later
//        LinkedHashSet<LLVMRelation> newSet;
//        // psi'
//        for (LLVMRelation rel : this) {
//            FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
//            newSet = new LinkedHashSet<LLVMRelation>(this);
//            newSet.remove(rel);
//            // is psi => phi satisfiable?, same like psi & !psi unsatisfiable
//            //SMTEngine smtEngine = new SMTLIBEngine();
//            SMTEngine yicesEngine = new YicesEngine();
//            Formula<SMTLIBTheoryAtom> psi = LLVMRelation.createSMTFormula(this);
//            Formula<SMTLIBTheoryAtom> phi = LLVMRelation.createSMTFormula(newSet);
//            Formula<SMTLIBTheoryAtom> psiAndNotPhi = factory.buildAnd(phi, factory.buildNot(psi));
//            //Formula<SMTLIBTheoryAtom> psiAndNotPhi = factory.buildAnd(psi, factory.buildNot(phi));
//            // TODO: Logic okay or should we use another logic?
//            // TODO: change names of variables
//            LinkedList<Formula<SMTLIBTheoryAtom>> psiAndNotPhiList = new LinkedList<Formula<SMTLIBTheoryAtom>>();
//            psiAndNotPhiList.add(psiAndNotPhi);
//            System.err.println("Try to remove: \"" + rel + "\" from: " + this);
//            YNM result;
//            try {
//                result = yicesEngine.satisfiable(psiAndNotPhiList, SMTLogic.QF_LIA, AbortionFactory.create());
//            } catch (WrongLogicException e) {
//                System.err.println("Solver error: " + e.getErrorMessage());
//                result = YNM.MAYBE;
//            }
//            if (result == YNM.NO) {
//                // unsatisfiable
//                this.clear();
//                this.addAll(newSet);
//                // TODO: remove this
//                System.err.println("Remove relation: \"" + rel + "\" after: " + this);
//            }
//        }
//    }

    @Override
    public boolean isEmpty() {
        return this.set.isEmpty();
    }

    @Override
    public Iterator<LLVMHeuristicRelation> iterator() {
        final Iterator<IntegerRelation> it = this.set.iterator();
        return
            new Iterator<LLVMHeuristicRelation>() {

                @Override
                public boolean hasNext() {
                    return it.hasNext();
                }

                @Override
                public LLVMHeuristicRelation next() {
                    return (LLVMHeuristicRelation)it.next();
                }

                @Override
                public void remove() {
                    it.remove();
                }

            };
    }

    /**
     * A solution of a relation set is defined as an assignment of values to
     * the variables of its relations, such that all relations hold. To merge
     * the solutions of two sets we intersect the sets themselves, thus
     * removing constraints and adding solutions.
     * This might also introduce new solutions.
     * @param other Some other relation set
     * @return A new relation set that describes a set of solutions ret, such
     *  that each solution for one of this or other is also a solution of the
     *  return value.
     */
    public LLVMHeuristicRelationSet mergeSolutions(LLVMHeuristicRelationSet other) {
        final LLVMHeuristicRelationSet returnValue = new LLVMHeuristicRelationSet();
        for (LLVMHeuristicRelation thisRelation : this) {
            for (LLVMHeuristicRelation otherRelation : other) {
                if (thisRelation.canRepresentStrictestSubsumingRelation(otherRelation)) {
                    returnValue.add(thisRelation.getStrictestSubsumingRelation(otherRelation));
                }
            }
        }
        return returnValue;
    }

    @Override
    public boolean remove(Object o) {
        return this.set.remove(o);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return this.set.removeAll(c);
    }

    /**
     * Removes all relations which contain the variable name at an
     * arbitrary position.
     * E.g. if varName="a" then a = b, z = 7 + a + c will be removed and relations
     * like  c = d + e stay untouched.
     * @param ref The reference.
     */
    public void removeRelations(LLVMHeuristicVariable ref) {
        this.set.removeRelations(ref);
    }

    /**
     * Replace all occurrences of one symbolic variable by another. Attention: This might yield tautological relations
     * which must be cleaned thereafter!
     * @param toReplaceVar The variable to replace.
     * @param replacementVar The variable that should be used instead.
     */
    public void replaceSymbolicVariable(LLVMHeuristicVariable toReplaceVar, LLVMHeuristicVariable replacementVar) {
        Set<LLVMHeuristicRelation> oldRelationSet = new LinkedHashSet<LLVMHeuristicRelation>(this);
        this.clear();
        for (LLVMHeuristicRelation rel : oldRelationSet) {
            this.add(rel.applySubstitution(toReplaceVar, replacementVar));
        }
    }

    /**
     * Restricts the relations to the passed set of references (while trying to keep transitive relations).
     * @param state The abstract state holding the knowledge about the references.
     * @param usedRefs set of used references.
     * @param params Strategy parameters.
     * @return True if the set is modified. False otherwise.
     */
    public LLVMHeuristicState restrictRelationsToRefs(
        LLVMHeuristicState state,
        Set<LLVMHeuristicVariable> usedRefs,
        LLVMParameters params,
        Abortion aborter
    ) {
        boolean changed = false;
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs = state.getAssociations();
        ImmutableMap<LLVMHeuristicVariable, BigInteger> assocOffsets = state.getAssociationOffsets();
        ImmutableList<LLVMAllocation> allocs = state.getAllocations();
        // first identify those relations containing unused references and delete them,
        // but store them and the unused references in extra sets for later use
        Iterator<LLVMHeuristicRelation> it = this.iterator();
        Set<LLVMHeuristicVariable> deletedRefs = new LinkedHashSet<LLVMHeuristicVariable>();
        LLVMHeuristicRelationSet deletedRels = new LLVMHeuristicRelationSet();
        while (it.hasNext()) {
            LLVMHeuristicRelation rel = it.next();
            boolean delete = false;
            for (LLVMHeuristicVariable ref : rel.getVariables(false)) {
                if (usedRefs.contains(ref)) {
                    continue;
                }
                delete = true;
                deletedRefs.add(ref);
            }
            if (delete) {
                it.remove();
                changed = true;
                if (rel.getHeuristicRelationType() != LLVMHeuristicRelationType.NE) {
                    // no checks are needed here
                    deletedRels.add(rel);
                }
            }
        }
        if (!changed) {
            return ProtectionUnlocker.UNLOCKER.setRelations(state, this);
        }
        final LLVMHeuristicRelationFactory factory = LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY;
        // for all deleted refs, add corresponding knowledge encoded by associations to deleted relations
        for (LLVMHeuristicVariable droppedRef : deletedRefs) {
            if (assocs.containsKey(droppedRef)) {
                LLVMAllocation allocation = allocs.get(assocs.get(droppedRef));
                deletedRels.add(factory.createRelation(IntegerRelationType.LE, allocation.x, droppedRef));
                deletedRels.add(
                    factory.createRelation(
                        IntegerRelationType.LE,
                        factory.getTermFactory().upperAddress(droppedRef, assocOffsets.get(droppedRef)),
                        allocation.y
                    )
                );
            }
        }
        // try to find equations between dropped refs and used refs together with constant factors/offsets
        // key = value.z * value.x + value.y
        Map<LLVMHeuristicVariable, Triple<LLVMHeuristicVariable, BigInteger, BigInteger>> replacements =
            new LinkedHashMap<LLVMHeuristicVariable, Triple<LLVMHeuristicVariable, BigInteger, BigInteger>>();
        for (LLVMHeuristicRelation rel : deletedRels.getEquations()) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
            if (!(lhsLinear.x instanceof LLVMHeuristicVariable && rhsLinear.x instanceof LLVMHeuristicVariable)) {
                continue;
            }
            if (deletedRefs.contains(lhsLinear.x)) {
                if (deletedRefs.contains(rhsLinear.x)) {
                    continue;
                }
                BigInteger offset = rhsLinear.y.subtract(lhsLinear.y);
                if (
                    offset.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) != 0
                    || rhsLinear.z.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) != 0
                ) {
                    continue;
                }
                offset = offset.divide(lhsLinear.z);
                BigInteger factor = rhsLinear.z.divide(lhsLinear.z);
                if (replacements.containsKey(lhsLinear.x)) {
                    Triple<LLVMHeuristicVariable, BigInteger, BigInteger> old = replacements.get(lhsLinear.x);
                    if (LLVMHeuristicRelationSet.betterMatch(offset, factor, old)) {
                        replacements.put(
                            (LLVMHeuristicVariable)lhsLinear.x,
                            new Triple<LLVMHeuristicVariable, BigInteger, BigInteger>(
                                (LLVMHeuristicVariable)rhsLinear.x,
                                offset,
                                factor
                            )
                        );
                    }
                } else {
                    replacements.put(
                        (LLVMHeuristicVariable)lhsLinear.x,
                        new Triple<LLVMHeuristicVariable, BigInteger, BigInteger>((LLVMHeuristicVariable)rhsLinear.x, offset, factor)
                    );
                }
            } else if (deletedRefs.contains(rhsLinear.x)) {
                BigInteger offset = lhsLinear.y.subtract(rhsLinear.y);
                if (
                    offset.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) != 0
                    || lhsLinear.z.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) != 0
                ) {
                    continue;
                }
                offset = offset.divide(rhsLinear.z);
                BigInteger factor = lhsLinear.z.divide(rhsLinear.z);
                if (replacements.containsKey(rhsLinear.x)) {
                    Triple<LLVMHeuristicVariable, BigInteger, BigInteger> old = replacements.get(rhsLinear.x);
                    if (LLVMHeuristicRelationSet.betterMatch(offset, factor, old)) {
                        replacements.put(
                            (LLVMHeuristicVariable)rhsLinear.x,
                            new Triple<LLVMHeuristicVariable, BigInteger, BigInteger>(
                                (LLVMHeuristicVariable)lhsLinear.x,
                                offset,
                                factor
                            )
                        );
                    }
                } else {
                    replacements.put(
                        (LLVMHeuristicVariable)rhsLinear.x,
                        new Triple<LLVMHeuristicVariable, BigInteger, BigInteger>(
                            (LLVMHeuristicVariable)lhsLinear.x,
                            offset,
                            factor
                        )
                    );
                }
            }
        }
        aborter.checkAbortion();
        final LLVMHeuristicTermFactory termFactory = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
        // build a substitution from the replacements
        Map<LLVMHeuristicVariable, LLVMHeuristicTerm> substitution =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicTerm>();
        for (
            Map.Entry<LLVMHeuristicVariable, Triple<LLVMHeuristicVariable, BigInteger, BigInteger>> entry :
                replacements.entrySet()
        ) {
            substitution.put(entry.getKey(), termFactory.create(entry.getValue()));
        }
        // replace refs and restore all relations which can now be expressed by used refs only
        LLVMHeuristicRelationSet stillDeletedRels = new LLVMHeuristicRelationSet();
        for (LLVMHeuristicRelation rel : deletedRels) {
            LLVMHeuristicRelation substRel = rel.applySubstitution(substitution);
            if (usedRefs.containsAll(substRel.getVariables(false))) {
                this.addRelation(
                    ProtectionUnlocker.UNLOCKER.setRelations(state, this).getIntegerState(),
                    substRel,
                    true,
                    aborter
                );
            } else {
                stillDeletedRels.add(substRel);
            }
        }
        /*
         * Now restore from each two relations of the form expr1 <= c + a * x and d + b * x <= expr2 where expr1
         * and expr2 only contain used refs and x is unused (turn strict relations into weak ones by adding/subtracting
         * 1) the relation (expr1 - c) a <= (expr2 - d) / b if the division is possible without any non-zero remainders.
         */
        // key >= expr
        Map<LLVMHeuristicVariable, Set<LLVMHeuristicTerm>> greater =
            new LinkedHashMap<LLVMHeuristicVariable, Set<LLVMHeuristicTerm>>();
        // key <= expr
        Map<LLVMHeuristicVariable, Set<LLVMHeuristicTerm>> less =
            new LinkedHashMap<LLVMHeuristicVariable, Set<LLVMHeuristicTerm>>();
        for (LLVMHeuristicRelation rel : stillDeletedRels.getDirectedInequalities()) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
            if (deletedRefs.contains(lhsLinear.x)) {
                BigInteger offsetWithoutDivision = rhsLinear.y.subtract(lhsLinear.y);
                if (rel.isStrictInequality()) {
                    offsetWithoutDivision = offsetWithoutDivision.subtract(BigInteger.ONE);
                }
                if (
                    rhsLinear.x == null
                    || !usedRefs.containsAll(rhsLinear.x.getVariables(false))
                    || rhsLinear.z.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) != 0
                    || offsetWithoutDivision.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) != 0
                ) {
                    continue;
                }
                if (!greater.containsKey(lhsLinear.x)) {
                    greater.put((LLVMHeuristicVariable)lhsLinear.x, new LinkedHashSet<LLVMHeuristicTerm>());
                }
                greater.get(
                    lhsLinear.x
                ).add(
                    termFactory.create(
                        new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                            rhsLinear.x,
                            offsetWithoutDivision.divide(lhsLinear.z),
                            rhsLinear.z.divide(lhsLinear.z)
                        )
                    )
                );
            } else if (deletedRefs.contains(rhsLinear.x)) {
                BigInteger offsetWithoutDivision = lhsLinear.y.subtract(rhsLinear.y);
                if (rel.isStrictInequality()) {
                    offsetWithoutDivision = offsetWithoutDivision.add(BigInteger.ONE);
                }
                if (
                    lhsLinear.x == null
                    || !usedRefs.containsAll(lhsLinear.x.getVariables(false))
                    || lhsLinear.z.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) != 0
                    || offsetWithoutDivision.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) != 0
                ) {
                    continue;
                }
                if (!less.containsKey(rhsLinear.x)) {
                    less.put((LLVMHeuristicVariable)rhsLinear.x, new LinkedHashSet<LLVMHeuristicTerm>());
                }
                less.get(
                    rhsLinear.x
                ).add(
                    termFactory.create(
                        new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                            lhsLinear.x,
                            offsetWithoutDivision.divide(rhsLinear.z),
                            lhsLinear.z.divide(rhsLinear.z)
                        )
                    )
                );
            }
        }
        Set<LLVMHeuristicVariable> bridges = new LinkedHashSet<LLVMHeuristicVariable>(greater.keySet());
        bridges.retainAll(less.keySet());
        for (LLVMHeuristicVariable bridge : bridges) {
            for (LLVMHeuristicTerm greaterExpr : greater.get(bridge)) {
                for (LLVMHeuristicTerm lessExpr : less.get(bridge)) {
                    this.addRelation(
                        ProtectionUnlocker.UNLOCKER.setRelations(state, this).getIntegerState(),
                        factory.createRelation(LLVMHeuristicRelationType.LE, lessExpr, greaterExpr),
                        true,
                        aborter
                    );
                }
            }
        }
        // finally remove relations over constants or values
        LLVMHeuristicState res = state;
        it = this.iterator();
        changed = true;
        while (changed) {
            changed = false;
            aborter.checkAbortion();
            while (it.hasNext()) {
                LLVMHeuristicRelation rel = it.next();
                LLVMHeuristicTerm relLhs = rel.getLhs();
                LLVMHeuristicTerm relRhs = rel.getRhs();
                if (relLhs instanceof LLVMHeuristicConstRef && relRhs instanceof LLVMHeuristicConstRef) {
                    it.remove();
                    if (Globals.useAssertions) {
                        assert (
                            LLVMHeuristicIntegerState.checkRelationOnConstants(
                                ((LLVMHeuristicConstRef)relLhs).getIntegerValue(),
                                rel.getHeuristicRelationType(),
                                ((LLVMHeuristicConstRef)relRhs).getIntegerValue()
                            )
                        ) : "Inconsistent relation detected!";
                    }
                } else {
                    Triple<LLVMHeuristicVariable, BigInteger, Boolean> valRel = rel.checkValueRelation();
                    if (valRel == null) {
                        continue;
                    }
                    it.remove();
                    if (valRel.z == null) {
                        LLVMReplacementResult next = res.unifySymbolicVariables(valRel.x, termFactory.constant(valRel.y));
                        res = next.x;
                        if (!next.y.isEmpty()) {
                            this.applySubstitution(next.y);
                            it = this.iterator();
                            changed = true;
                            break;
                        }
                    } else if (valRel.z) {
                        LLVMValue value = res.getValue(valRel.x);
                        AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
                        IntervalBound upper = val.getUpper();
                        if (!upper.isFinite() || upper.getConstant().compareTo(valRel.y) > 0) {
                        	AbstractBoundedInt nVal = val.setUpper(IntervalBound.create(valRel.y));
                        	if(nVal == null) {
                        		throw new InconsistentStateException(null, null);
                        	}
                            res = res.setValue(valRel.x, nVal);
                        }
                    } else {
                        LLVMValue value = res.getValue(valRel.x);
                        AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
                        IntervalBound lower = val.getLower();
                        if (!lower.isFinite() || lower.getConstant().compareTo(valRel.y) < 0) {
                        	AbstractBoundedInt afterLower = val.setLower(IntervalBound.create(valRel.y));
                        	if(afterLower == null) {
                        		throw new InconsistentStateException(null, null);
                        	}
                            res = res.setValue(valRel.x, afterLower);
                        }
                    }
                }
            }
        }
        return ProtectionUnlocker.UNLOCKER.setRelations(res, this).cleanRelations(aborter);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return this.set.retainAll(c);
    }

    @Override
    public int size() {
        return this.set.size();
    }

    @Override
    public Object[] toArray() {
        return this.set.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return this.set.toArray(a);
    }

    /**
     * Creates an SMT expression from this relation set.
     * @return An SMT expression representing the conjunction of the relations in this set.
     */
    @Override
    public SMTExpression<SBool> toSMTExp() {
        return this.set.toSMTExp();
    }

    @Override
    public String toString() {
        return this.set.toString();
    }

    /**
     * Unlocks protection for some protected methods in LLVMHeuristicState.
     * @author cryingshadow
     * @version $Id$
     */
    private static class ProtectionUnlocker extends LLVMHeuristicState.ProtectionAnchor {

        /**
         * Instance for unlocking protection.
         */
        private static final ProtectionUnlocker UNLOCKER = new ProtectionUnlocker();

        @Override
        protected LLVMHeuristicState setRelations(LLVMHeuristicState state, Set<LLVMHeuristicRelation> rels) {
            return super.setRelations(state, rels);
        }

    }

}
