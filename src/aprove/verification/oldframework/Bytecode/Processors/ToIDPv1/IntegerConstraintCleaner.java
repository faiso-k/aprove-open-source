package aprove.verification.oldframework.Bytecode.Processors.ToIDPv1;

import java.lang.reflect.*;
import java.math.*;
import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * TODO unify structures used for integer expressions
 * Convenience class containing the code needed to clean a set of
 * (conjunctive) integer constraints. The cleaning is done iteratively
 * until a fixpoint is reached, using the following rules (iK denoting
 * some abstract int, cK a known constant int):
 *
 * <!-- If you feel this looks like a TRS ... you are right! -->
 *
 * <ul>
 *  <li> "i1 = i2 (+|-) 0" or "i1 = 0 (+|-) i2" or "0 = i1 - i2" become i1 = i2
 *  <li> "i1 = i2 (*|/) 1" or "i1 = 1 * i2" become i1 = i2
 *  <li> "i1 = c1 (+|-|*|/) c2" are computed (result c3) and become i1 = c3
 *  <li> "c1 = i1 (+|-|*|/) c2" or "c1 = c2 (+|-|*|/) i1" are shuffled around
 *   till i1 is alone on one side
 * </ul>
 *
 * Pairs of integer relations are also handled (listed for >=, naturally
 * also done for <=):
 * <ul>
 *  <li> "i1 = i2" (w.l.o.g. i1 not a constant) becomes a substitution [i1/i2]
 *   applied to all constraints and also stored for later use on terms.
 *  <li> "i1 >= i2 && i1 <= i2" becomes i1 = i2
 *  <li> "i1 >= i2 && i1 > i2" becomes i1 > i2
 *  <li> "i1 (>|>=) i2 && i1 != i2" becomes i1 > i2
 *  <li> "i1 (>=|>) c1 && i1 > c2 && c1 > c2" becomes i1 (>=|>) c1
 *  <li> "i1 (>=|>) i2 && i1 < i2" becomes FALSE
 * </ul>
 *
 * @author Marc Brockschmidt, Christian von Essen
 */
public final class IntegerConstraintCleaner {

    public static final FunctionSymbol INTERNAL_MAX_SYMBOL =
        FunctionSymbol.create(RuleCreator.INTERNAL_MAX_SYMBOL.getName(),
        RuleCreator.INTERNAL_MAX_SYMBOL.getArity());

    private static final IDPPredefinedMap SYM_MAP = IDPPredefinedMap.DEFAULT_MAP;

    public static Pair<TRSTerm, TRSSubstitution> clean(
        final TRSTerm app,
        final boolean forceMaxAway,
        final boolean kittelsupport,
        final Abortion aborter
    ) throws AbortionException {
        final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        final List<IntegerConstraintRelation> relations = IntegerConstraintCleaner.takeApart(app, fne);
        IntegerConstraintCleaner.perform(relations, forceMaxAway, kittelsupport, fne, aborter);
        final TRSSubstitution resSubst = IntegerConstraintCleaner.splitOutSubstitutions(relations);
        TRSTerm cleanedConstraint = IntegerConstraintCleaner.conjunction(relations);
        if (cleanedConstraint != null) {
            cleanedConstraint = cleanedConstraint.applySubstitution(resSubst);
        }
        //Canonical order of relations:
        Collections.sort(relations);
        return new Pair<TRSTerm, TRSSubstitution>(cleanedConstraint, resSubst);
    }

    public static TRSTerm conjunction(final List<IntegerConstraintRelation> relations) {
        TRSTerm result = null;
        for (final IntegerConstraintRelation rel : relations) {
            result = IDPv2ToIDPv1Utilities.getConjunction(result, rel.toDPTerm());
        }
        return result;
    }

    /** Pairs of integer relations are also handled (listed for >=, naturally
     * also done for <=):
     * <ul>
     *  <li> "i1 >= i2 && i1 <= i2" becomes i1 = i2
     *  <li> "i1 >= i2 && i1 > i2" becomes i1 > i2
     *  <li> "i1 (>|>=) i2 && i1 != i2" becomes i1 > i2
     *  <li> "i1 (>=|>) c1 && i1 > c2 && c1 > c2" becomes i1 (>=|>) c1
     *  <li> "i1 (>|>=) i2" && "i1 \1 i2 + c1" becomes "i1 \1 i2 + c1" if c1 is
     *   positive (and the symmetric case)
     * </ul>
     *
     * @param rel1
     * @param rel2
     * @return A new relation implied by rel1 and rel2
     */
    public static IntegerConstraintRelation implication(
        final IntegerConstraintRelation rel1,
        final IntegerConstraintRelation rel2
    ) {
        final IntegerConstraintTerm rel1Left = rel1.getLeft();
        final IntegerConstraintTerm rel1Right = rel1.getRight();
        final IntegerConstraintTerm rel2Left = rel2.getLeft();
        final IntegerConstraintTerm rel2Right = rel2.getRight();
        if (
            rel1 instanceof IntegerConstraintGE
            && rel2 instanceof IntegerConstraintLE
            && rel1Left.equals(rel2Left)
            && rel1Right.equals(rel2Right)
        ) {
            return new IntegerConstraintEQ(rel1Left, rel1Right, false);
        }
        if (
            rel1 instanceof IntegerConstraintGE
            && rel2 instanceof IntegerConstraintGT
            && rel1Left.equals(rel2Left)
            && rel1Right.equals(rel2Right)
        ) {
            return new IntegerConstraintGT(rel1Left, rel1Right, false);
        }
        if (
            (rel1 instanceof IntegerConstraintGE || rel1 instanceof IntegerConstraintGT)
            && rel2 instanceof IntegerConstraintNE
            && (
                (rel1Left.equals(rel2Left) && rel1Right.equals(rel2Right))
                || (rel1Left.equals(rel2Right) && rel1Right.equals(rel2Left))
            )
        ) {
            return new IntegerConstraintGT(rel1Left, rel1Right, false);
        }
        if (rel1Left.equals(rel2Left)) {
            if (rel1Right.isVariable() && (rel2Right.isAdd() || rel2Right.isSub())) {
                final BinaryIntegerConstraintOperation rel2RightOp = (BinaryIntegerConstraintOperation) rel2Right;
                if (
                    (rel1 instanceof IntegerConstraintGE || rel1 instanceof IntegerConstraintGT)
                    && (
                        rel2.getClass().isInstance(rel1)
                        && (
                            (
                                rel2RightOp.getLeft().equals(rel1Right)
                                && rel2RightOp.getRight().isConstant()
                                && ((IntegerConstraintConstant)rel2RightOp.getRight()).value.compareTo(
                                    BigInteger.ZERO
                                ) >= 0
                            ) || (
                                rel2RightOp.getRight().equals(rel1Right)
                                && rel2RightOp.getLeft().isConstant()
                                && ((IntegerConstraintConstant)rel2RightOp.getLeft()).value.compareTo(
                                    BigInteger.ZERO
                                ) >= 0
                            )
                        )
                    )
                ) {
                    return rel2;
                }
            }
            if (rel1Right.isConstant() && rel2Right.isConstant()) {
                final IntegerConstraintConstant rel1RightConst = (IntegerConstraintConstant)rel1Right;
                final IntegerConstraintConstant rel2RightConst = (IntegerConstraintConstant)rel2Right;
                if (
                    (rel1 instanceof IntegerConstraintGT)
                    && (rel2 instanceof IntegerConstraintGT || rel2 instanceof IntegerConstraintGE)
                    && rel1RightConst.compareTo(rel2RightConst) > 0
                ) {
                    return new IntegerConstraintGT(rel1Left, rel1Right, false);
                }

                if (
                    (rel1 instanceof IntegerConstraintGE)
                    && (rel2 instanceof IntegerConstraintGE || rel2 instanceof IntegerConstraintGT)
                    && rel1RightConst.compareTo(rel2RightConst) > 0
                ) {
                    return new IntegerConstraintGE(rel1Left, rel1Right, false);
                }
            }
        }
        return null;
    }

    /**
     * Return true iff a part of integer relations does not have a model (i.e., implies FALSE).
     * @param rel1
     * @param rel2
     * @return A new relation implied by rel1 and rel2
     */
    public static boolean impliesFalse(final IntegerConstraintRelation rel1, final IntegerConstraintRelation rel2) {
        final IntegerConstraintTerm rel1Left = rel1.getLeft();
        final IntegerConstraintTerm rel1Right = rel1.getRight();
        final IntegerConstraintTerm rel2Left = rel2.getLeft();
        final IntegerConstraintTerm rel2Right = rel2.getRight();
        if (rel1 instanceof IntegerConstraintFALSE || rel2 instanceof IntegerConstraintFALSE) {
            return true;
        }
        // x (>=|>|=) y && x < y
        if (
            (
                rel1 instanceof IntegerConstraintGE
                || rel1 instanceof IntegerConstraintGT
                || rel1 instanceof IntegerConstraintEQ
            )
            && rel2 instanceof IntegerConstraintLT
            && rel1Left.equals(rel2Left)
            && rel1Right.equals(rel2Right)
        ) {
            return true;
        }

        // x (<=|<|=) y && x > y
        if (
            (
                rel1 instanceof IntegerConstraintLE
                || rel1 instanceof IntegerConstraintLT
                || rel1 instanceof IntegerConstraintEQ
            )
            && rel2 instanceof IntegerConstraintGT
            && rel1Left.equals(rel2Left)
            && rel1Right.equals(rel2Right)
        ) {
            return true;
        }
        return false;
    }

    public static boolean isTautology(final IntegerConstraintRelation rel, final boolean kittelsupport) {
        final IntegerConstraintTerm left = rel.getLeft();
        final IntegerConstraintTerm right = rel.getRight();
        return
            (rel instanceof IntegerConstraintTRUE)
            || (
                (
                    rel instanceof IntegerConstraintGE
                    || rel instanceof IntegerConstraintLE
                    || rel instanceof IntegerConstraintEQ
                ) && left.equals(right)
            );
    }

    public static IntegerConstraintTerm moveMaxesToFreshVars(
        final IntegerConstraintTerm t,
        final FreshNameGenerator fne,
        final Map<IntegerConstraintTerm, IntegerConstraintVariable> maxToVarMap,
        final Position pos,
        final List<IntegerConstraintRelation> constraints
    ) {
        if (t.isConstant() || t.isVariable()) {
            return t;
        }
        assert (t instanceof BinaryIntegerConstraintOperation);
        //Ok, we have a binary operation:
        final BinaryIntegerConstraintOperation cur = (BinaryIntegerConstraintOperation)t;
        final IntegerConstraintTerm newLeft =
            IntegerConstraintCleaner.moveMaxesToFreshVars(cur.getLeft(), fne, maxToVarMap, pos.append(0), constraints);
        final IntegerConstraintTerm newRight =
            IntegerConstraintCleaner.moveMaxesToFreshVars(cur.getRight(), fne, maxToVarMap, pos.append(1), constraints);
        final BinaryIntegerConstraintOperation newRel = cur.newInstance(newLeft, newRight);
        if (newRel.isMax()) {
            IntegerConstraintVariable newVar = maxToVarMap.get(newRel);
            if (newVar == null) {
                newVar = new IntegerConstraintVariable(fne.getFreshName("freshMax" + pos.toString(), false));
                maxToVarMap.put(newRel, newVar);
                constraints.add(new IntegerConstraintEQ(newVar, newRel, false));
            }
            return newVar;
        } else {
            return newRel;
        }
    }

    public static List<IntegerConstraintRelation> moveMaxesToFreshVars(
        final List<IntegerConstraintRelation> constraints,
        final FreshNameGenerator fne
    ) {
        final List<IntegerConstraintRelation> workingCopy = new ArrayList<IntegerConstraintRelation>();
        final Map<IntegerConstraintTerm, IntegerConstraintVariable> maxToVarMap =
            new LinkedHashMap<IntegerConstraintTerm, IntegerConstraintVariable>();
        for (final IntegerConstraintRelation rel : constraints) {
            final IntegerConstraintTerm left = rel.getLeft();
            final IntegerConstraintTerm right = rel.getRight();
            final IntegerConstraintTerm newLeft;
            if (!(rel instanceof IntegerConstraintEQ) || left.containsMax()) {
                newLeft =
                    IntegerConstraintCleaner.moveMaxesToFreshVars(
                        left,
                        fne,
                        maxToVarMap,
                        Position.create(0),
                        workingCopy
                    );
            } else {
                newLeft = left;
            }
            final IntegerConstraintTerm newRight;
            if (!(rel instanceof IntegerConstraintEQ) || right.containsMax()) {
                newRight =
                    IntegerConstraintCleaner.moveMaxesToFreshVars(
                        right,
                        fne,
                        maxToVarMap,
                        Position.create(1),
                        workingCopy
                    );
            } else {
                newRight = right;
            }
            workingCopy.add(rel.newInstance(newLeft, newRight, rel.negated));
        }
        return workingCopy;
    }

    public static boolean perform(
        final ImmutableList<IntegerConstraintRelation> relations,
        final boolean kittelsupport,
        final List<IntegerConstraintRelation> result,
        final FreshNameGenerator fne
    ) {
        // Let us first try to simplify the terms contained in the relations
        boolean changed = false;
        for (final IntegerConstraintRelation rel : relations) {
            if (IntegerConstraintCleaner.isTautology(rel, kittelsupport)) {
                changed = true;
                continue;
            }
            final IntegerConstraintRelation simplified =
                IntegerConstraintCleaner.simplifyRelation(rel.canonicalize(), kittelsupport);
            if (simplified != rel) {
                changed = true;
            }
            result.add(simplified);
        }
        // Now let us look if we can find any implication
        final List<IntegerConstraintRelation> toBeRemoved = new ArrayList<IntegerConstraintRelation>();
        final List<IntegerConstraintRelation> implied = new ArrayList<IntegerConstraintRelation>();
        outer: for (final ListIterator<IntegerConstraintRelation> it1 = result.listIterator(); it1.hasNext();) {
            final IntegerConstraintRelation rel1 = it1.next();
            final IntegerConstraintRelation rel1Inverted = rel1.invert();
            for (final ListIterator<IntegerConstraintRelation> it2 = result.listIterator(); it2.hasNext();) {
                final IntegerConstraintRelation rel2 = it2.next();
                if (rel1 == rel2) {
                    continue;
                }
                final IntegerConstraintRelation rel2Inverted = rel2.invert();
                final boolean impliesFALSE =
                    IntegerConstraintCleaner.impliesFalse(rel1, rel2)
                    || IntegerConstraintCleaner.impliesFalse(rel1Inverted, rel2)
                    || IntegerConstraintCleaner.impliesFalse(rel1, rel2Inverted)
                    || IntegerConstraintCleaner.impliesFalse(rel1Inverted, rel2Inverted);
                if (impliesFALSE) {
                    changed = true;
                    result.clear();
                    toBeRemoved.clear();
                    result.add(new IntegerConstraintFALSE(null, null, false));
                    break outer;
                }
                final IntegerConstraintRelation implication = IntegerConstraintCleaner.implication(rel1, rel2);
                final IntegerConstraintRelation firstInvertedImplication =
                    IntegerConstraintCleaner.implication(rel1Inverted, rel2);
                final IntegerConstraintRelation secondInvertedImplication =
                    IntegerConstraintCleaner.implication(rel1, rel2Inverted);
                final IntegerConstraintRelation bothInvertedImplication =
                    IntegerConstraintCleaner.implication(rel1Inverted, rel2Inverted);
                if (
                    implication != null
                    || firstInvertedImplication != null
                    || secondInvertedImplication != null
                    || bothInvertedImplication != null
                ) {
                    toBeRemoved.add(rel1);
                    toBeRemoved.add(rel2);
                    changed = true;
                }
                if (implication != null) {
                    implied.add(implication);
                } else if (firstInvertedImplication != null) {
                    implied.add(firstInvertedImplication);
                } else if (secondInvertedImplication != null) {
                    implied.add(secondInvertedImplication);
                } else if (bothInvertedImplication != null) {
                    implied.add(bothInvertedImplication);
                }
            }
        }
        result.removeAll(toBeRemoved);
        result.addAll(implied);
        // Finally, try to apply all substitutions
        for (final ListIterator<IntegerConstraintRelation> it = result.listIterator(); it.hasNext();) {
            final IntegerConstraintRelation rel = it.next();
            if (rel instanceof IntegerConstraintEQ && !rel.containsMax()) {
                if (rel.getLeft().isVariable()) {
                    final IntegerConstraintVariable left = (IntegerConstraintVariable) rel.getLeft();
                    if (rel.getRight().getVariables().contains(left) || rel.getRight().isDiv()) {
                        continue;
                    }
                    final IntegerConstraintTerm right = IntegerConstraintCleaner.simplifyTerm(rel.getRight(), kittelsupport);
                    for (final ListIterator<IntegerConstraintRelation> it2 = result.listIterator(); it2.hasNext();) {
                        final IntegerConstraintRelation rel2 = it2.next();
                        if (rel2 != rel && rel2.getVariables().contains(left)) {
                            final IntegerConstraintRelation newRel2 = rel2.substitute(left, right);
                            if (!newRel2.equals(rel2)) {
                                it2.set(newRel2);
                                changed = true;
                            }
                        }
                    }
                } else if (rel.getRight().isVariable()) {
                    final IntegerConstraintVariable right = (IntegerConstraintVariable) rel.getRight();
                    if (rel.getLeft().getVariables().contains(right) || rel.getLeft().isDiv()) {
                        continue;
                    }
                    final IntegerConstraintTerm left = IntegerConstraintCleaner.simplifyTerm(rel.getLeft(), kittelsupport);
                    for (final ListIterator<IntegerConstraintRelation> it2 = result.listIterator(); it2.hasNext();) {
                        final IntegerConstraintRelation rel2 = it2.next();
                        if (rel2 != rel && rel2.getVariables().contains(right)) {
                            final IntegerConstraintRelation newRel2 = rel2.substitute(right, left);
                            if (!newRel2.equals(rel2)) {
                                it2.set(newRel2);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        return changed;
    }

    public static void perform(
        final List<IntegerConstraintRelation> constraints,
        final boolean forceMaxAway,
        final boolean kittelsupport,
        final FreshNameGenerator fne,
        final Abortion aborter
    ) throws AbortionException {
        List<IntegerConstraintRelation> workingCopy = new ArrayList<IntegerConstraintRelation>(constraints);
        boolean changed = false;
        do {
            aborter.checkAbortion();
            changed = false;
            final List<IntegerConstraintRelation> result = new ArrayList<IntegerConstraintRelation>();
            changed |=
                IntegerConstraintCleaner.perform(ImmutableCreator.create(workingCopy), kittelsupport, result, fne);
            if (forceMaxAway) {
                changed |= IntegerConstraintCleaner.approximateMaxes(result, fne, aborter);
            } else {
                changed |= IntegerConstraintCleaner.tryToResolveMaxes(result, fne, aborter);
            }
            workingCopy = result;
        } while (changed);
        constraints.clear();
        constraints.addAll(workingCopy);
    }

    /**
     * "c1 = i1 (+|-|*|/) c2" or "c1 = c2 (+|-|*|/) i1" are shuffled around till i1 is alone on one side.
     * @param eq
     * @return
     */
    public static IntegerConstraintEQ rotate(final IntegerConstraintEQ eq) {
        final IntegerConstraintTerm left = eq.getLeft();
        final IntegerConstraintTerm right = eq.getRight();
        if (!left.isConstant()) {
            return null;
        }
        if (!(right instanceof BinaryIntegerConstraintOperation)) {
            return null;
        }
        final BinaryIntegerConstraintOperation binOp = (BinaryIntegerConstraintOperation) right;
        // at least one of the operands has to be a constant, while the other one has to be a variable
        if (
            !(
                (binOp.getLeft().isVariable() && binOp.getRight().isConstant())
                || (binOp.getLeft().isConstant() && binOp.getRight().isVariable())
            )
        ) {
            return null;
        }
        if (binOp.getRight().isConstant()) {
            //  c1 = i1 (+|-|*|/) c2
            if (binOp.isAdd()) {
                return
                    new IntegerConstraintEQ(binOp.getLeft(), new IntegerConstraintSub(left, binOp.getRight()), false);
            } else if (binOp.isSub()) {
                return
                    new IntegerConstraintEQ(binOp.getLeft(), new IntegerConstraintAdd(left, binOp.getRight()), false);
            } else if (binOp.isMul()) {
                return
                    new IntegerConstraintEQ(binOp.getLeft(), new IntegerConstraintDiv(left, binOp.getRight()), false);
            } else if (binOp.isDiv()) {
                return
                    new IntegerConstraintEQ(binOp.getLeft(), new IntegerConstraintMul(left, binOp.getRight()), false);
            } else {
                return null;
            }
        } else {
            //  c1 = c2 (+|-|*|/) i1
            if (binOp.isAdd()) {
                return
                    new IntegerConstraintEQ(binOp.getLeft(), new IntegerConstraintSub(binOp.getRight(), left), false);
            } else if (binOp.isSub()) {
                return
                    new IntegerConstraintEQ(binOp.getLeft(), new IntegerConstraintSub(binOp.getRight(), left), false);
            } else if (binOp.isMul()) {
                return
                    new IntegerConstraintEQ(binOp.getLeft(), new IntegerConstraintDiv(binOp.getRight(), left), false);
            } else if (binOp.isDiv()) {
                return
                    new IntegerConstraintEQ(binOp.getLeft(), new IntegerConstraintDiv(binOp.getRight(), left), false);
            } else {
                return null;
            }
        }
    }

    public static IntegerConstraintRelation simplifyRelation(
        final IntegerConstraintRelation rel,
        final boolean kittelsupport
    ) {
        final IntegerConstraintTerm left = rel.getLeft();
        final IntegerConstraintTerm right = rel.getRight();
        if (
            left instanceof IntegerConstraintConstant
            && right instanceof IntegerConstraintConstant
            && !((rel instanceof IntegerConstraintFALSE) || (rel instanceof IntegerConstraintTRUE))
        ) {
            final long leftVal = ((IntegerConstraintConstant) left).getValue().longValue();
            final long rightVal = ((IntegerConstraintConstant) right).getValue().longValue();
            if (
                (rel instanceof IntegerConstraintEQ && leftVal == rightVal)
                || (rel instanceof IntegerConstraintNE && leftVal != rightVal)
                || (rel instanceof IntegerConstraintLE && leftVal <= rightVal)
                || (rel instanceof IntegerConstraintLT && leftVal < rightVal)
                || (rel instanceof IntegerConstraintGE && leftVal >= rightVal)
                || (rel instanceof IntegerConstraintGT && leftVal > rightVal)
            ) {
                return new IntegerConstraintTRUE();
            } else if (
                (rel instanceof IntegerConstraintEQ && leftVal != rightVal)
                || (rel instanceof IntegerConstraintNE && leftVal == rightVal)
                || (rel instanceof IntegerConstraintLE && leftVal > rightVal)
                || (rel instanceof IntegerConstraintLT && leftVal >= rightVal)
                || (rel instanceof IntegerConstraintGE && leftVal < rightVal)
                || (rel instanceof IntegerConstraintGT && leftVal <= rightVal)
            ) {
                return new IntegerConstraintFALSE();
            } else {
                assert (false) : leftVal + " " + rel + " " + rightVal + " is decidable.";
            }
        }
        final IntegerConstraintTerm simplifiedLeft = IntegerConstraintCleaner.simplifyTerm(left, kittelsupport);
        final IntegerConstraintTerm simplifiedRight = IntegerConstraintCleaner.simplifyTerm(right, kittelsupport);
        if (!left.equals(simplifiedLeft) || !right.equals(simplifiedRight)) {
            return
                IntegerConstraintCleaner.simplifyRelation(
                    rel.newInstance(simplifiedLeft, simplifiedRight, rel.isNegated()),
                    kittelsupport
                );
        } else {
            final IntegerConstraintRelation newRel = IntegerConstraintCleaner.reduceConstants(rel);
            if (newRel != rel) {
                return IntegerConstraintCleaner.simplifyRelation(newRel, kittelsupport);
            } else {
                final IntegerConstraintRelation relInv = rel.invert();
                final IntegerConstraintRelation newRelInv = IntegerConstraintCleaner.reduceConstants(relInv);
                if (newRelInv != relInv) {
                    return IntegerConstraintCleaner.simplifyRelation(newRelInv, kittelsupport);
                }
            }
        }
        //Normalize x >= c to x > c - 1 and x <= c to x < c + 1
        if (left.isVariable() && right.isConstant()) {
            if (rel instanceof IntegerConstraintGE) {
                return
                    IntegerConstraintCleaner.simplifyRelation(
                        new IntegerConstraintGT(
                            left,
                            new IntegerConstraintAdd(right, new IntegerConstraintConstant(-1)),
                            rel.negated
                        ),
                        kittelsupport
                    );
            } else if (rel instanceof IntegerConstraintLE) {
                return
                    IntegerConstraintCleaner.simplifyRelation(
                        new IntegerConstraintLT(
                            left,
                            new IntegerConstraintAdd(right, new IntegerConstraintConstant(1)),
                            rel.negated
                        ),
                        kittelsupport
                    );
            }
        } else if (right.isVariable() && left.isConstant()) {
            if (rel instanceof IntegerConstraintGE) {
                return
                    IntegerConstraintCleaner.simplifyRelation(
                        new IntegerConstraintGT(
                            new IntegerConstraintAdd(left, new IntegerConstraintConstant(1)),
                            right,
                            rel.negated
                        ),
                        kittelsupport
                    );
            } else if (rel instanceof IntegerConstraintLE) {
                return
                    IntegerConstraintCleaner.simplifyRelation(
                        new IntegerConstraintLT(
                            new IntegerConstraintAdd(left, new IntegerConstraintConstant(-1)),
                            right,
                            rel.negated
                        ),
                        kittelsupport
                    );
            }
        }
        return rel;
    }

    /**
     * We simplify the given term t according to the following rules:
     *
     * If t is a variable or a constant, then nothing happens.
     * Otherwise, we know that t is a binary operation (i.e., an instance of {@link BinaryIntegerConstraintOperation}.
     *
     * We first look if one or both operands can be simplified. If so, then we return
     * a new term, denoting the same operations but with the simplified operands.
     *
     * Afterwards the term is simplified according to the following rules.
     *
     * Now let c1 and c2 represent constants.
     *
     * <ul>
     *   <li> t = c1 (+|-|*|/|%) c2 then we execute the operation and return the resulting constant </li>
     *   <li> t = t' (+|-) 0 is mapped to t' </li>
     *   <li> t = t' (*|/) 1 is mapped to t' </li>
     *   <li> t = t' (*|/) 0 is mapped to 0 </li>
     *   <li> t = 0  +    t' is mapped to t' </li>
     *   <li> t = 1  *    t' is mapped to t' </li>
     * </ul>
     *
     * @param t Term to simplify
     * @return The simplified term, if simplification was possible. Otherwise t is returned.
     */
    public static IntegerConstraintTerm simplifyTerm(final IntegerConstraintTerm t, final boolean kittelsupport) {
        if (t.isVariable() || t.isConstant()) {
            return t;
        }
        if (Globals.useAssertions) {
            assert (t instanceof BinaryIntegerConstraintOperation);
        }
        final IntegerConstraintTerm leftOp = ((BinaryIntegerConstraintOperation) t).getLeft();
        final IntegerConstraintTerm rightOp = ((BinaryIntegerConstraintOperation) t).getRight();
        // See whether it is possible to simplify one or both operands
        final IntegerConstraintTerm simplifiedLeft = IntegerConstraintCleaner.simplifyTerm(leftOp, kittelsupport);
        final IntegerConstraintTerm simplifiedRight = IntegerConstraintCleaner.simplifyTerm(rightOp, kittelsupport);
        if (simplifiedLeft != leftOp || simplifiedRight != rightOp) {
            return ((BinaryIntegerConstraintOperation) t).newInstance(simplifiedLeft, simplifiedRight);
        }
        // If both sides are constants, then we can simply calculate the result
        if (leftOp.isConstant() && rightOp.isConstant()) {
            final BigInteger leftVal = ((IntegerConstraintConstant) leftOp).getValue();
            final BigInteger rightVal = ((IntegerConstraintConstant) rightOp).getValue();
            if (t.isAdd()) {
                return new IntegerConstraintConstant(leftVal.add(rightVal));
            } else if (t.isSub()) {
                return new IntegerConstraintConstant(leftVal.subtract(rightVal));
            } else if (t.isMul()) {
                return new IntegerConstraintConstant(leftVal.multiply(rightVal));
            } else if (t.isDiv()) {
                return new IntegerConstraintConstant(leftVal.divide(rightVal));
            } else if (t.isMod()) {
                return new IntegerConstraintConstant(leftVal.remainder(rightVal));
            } else if (t.isMax()) {
                return new IntegerConstraintConstant(leftVal.max(rightVal));
            } else {
                assert (false) : "This code should never be reached.";
            }
        }
        // rightOp = 0
        if (rightOp.isConstant() && ((IntegerConstraintConstant) rightOp).getValue().equals(BigInteger.ZERO)) {
            // t = t' (+|-) 0 -> t'
            if (t.isAdd() || t.isSub()) {
                return leftOp;
            }
            // t = t' * 0     -> 0
            if (t.isMul()) {
                return rightOp;
            }
        }
        // rightOp = 1
        if (rightOp.isConstant() && ((IntegerConstraintConstant) rightOp).getValue().equals(BigInteger.ONE)) {
            // t = t' (*|/) 1 -> t'
            if (t.isMul() || t.isDiv()) {
                return leftOp;
            }
        }
        // leftOp = 0
        if (leftOp.isConstant() && ((IntegerConstraintConstant) leftOp).getValue().equals(BigInteger.ZERO)) {
            // t = 0 + t' -> t'
            if (t.isAdd()) {
                return rightOp;
            }
            // t = 0 (*|/) t' -> 0
            if (t.isMul() || t.isDiv()) {
                return leftOp;
            }
        }
        // leftOp = 1
        if (leftOp.isConstant() && ((IntegerConstraintConstant) leftOp).getValue().equals(BigInteger.ONE)) {
            // t = 1 * t' -> t'
            if (t.isMul()) {
                return rightOp;
            }
        }
        // this = leftOp OP rightOp, leftOp = x OP const1, rightOp = const2
        if (leftOp.getClass().equals(t.getClass())) {
            final IntegerConstraintTerm leftLeftOp = ((BinaryIntegerConstraintOperation) leftOp).getLeft();
            final IntegerConstraintTerm leftRightOp = ((BinaryIntegerConstraintOperation) leftOp).getRight();
            if (rightOp.isConstant() && leftRightOp.isConstant()) {
                if (leftOp.isAdd()) {
                    return
                        IntegerConstraintCleaner.simplifyTerm(
                            new IntegerConstraintAdd(
                                leftLeftOp,
                                new IntegerConstraintConstant(
                                    ((IntegerConstraintConstant)leftRightOp).getValue().add(
                                        ((IntegerConstraintConstant)rightOp).getValue()
                                    )
                                )
                            ),
                            kittelsupport
                        );
                } else if (leftOp.isMul()) {
                    return
                        IntegerConstraintCleaner.simplifyTerm(
                            new IntegerConstraintMul(
                                leftLeftOp,
                                new IntegerConstraintConstant(
                                    ((IntegerConstraintConstant)leftRightOp).getValue().multiply(
                                        ((IntegerConstraintConstant)rightOp).getValue()
                                    )
                                )
                            ),
                            kittelsupport
                        );
                }
                //Lots a more cases, I'm just lazy
            }
        }
        // move MULTs away
        if (kittelsupport && t.isMul() && (!leftOp.isAtom() || !rightOp.isAtom())) {
            if (!leftOp.isAtom()) {
                return IntegerConstraintCleaner.distributeMUL((BinaryIntegerConstraintOperation) leftOp, rightOp);
            } else {
                return IntegerConstraintCleaner.distributeMUL((BinaryIntegerConstraintOperation) rightOp, leftOp);
            }
        }
        //Normalize to right side:
        if (kittelsupport && t.isMul() && (leftOp.isVariable()) && (rightOp.isConstant())) {
            return ((BinaryIntegerConstraintOperation) t).newInstance(rightOp, leftOp);
        }
        return t;
    }

    public static List<IntegerConstraintRelation> takeApart(final TRSTerm constraint, final FreshNameGenerator fne) {
        final List<TRSFunctionApplication> toDo = new ArrayList<TRSFunctionApplication>();
        final List<IntegerConstraintRelation> result = new ArrayList<IntegerConstraintRelation>();
        if (constraint instanceof TRSFunctionApplication) {
            toDo.add((TRSFunctionApplication) constraint);
        } else {
            result.add(new IntegerConstraintTRUE());
        }
        while (!toDo.isEmpty()) {
            final TRSFunctionApplication app = toDo.remove(0);
            if (IntegerConstraintCleaner.SYM_MAP.isLand(app.getRootSymbol())) {
                assert (app.getArgument(0) instanceof TRSFunctionApplication);
                assert (app.getArgument(1) instanceof TRSFunctionApplication);
                toDo.add((TRSFunctionApplication) app.getArgument(0));
                toDo.add((TRSFunctionApplication) app.getArgument(1));
            } else if (IntegerConstraintCleaner.SYM_MAP.isBooleanFalse(app.getRootSymbol())) {
                result.add(new IntegerConstraintFALSE());
            } else {
                result.add(IntegerConstraintCleaner.toRelation(app, fne).normalize());
            }
        }
        return result;
    }

    public static boolean tryToResolveMaxes(
        final List<IntegerConstraintRelation> constraints,
        final FreshNameGenerator fne,
        final Abortion aborter
    ) throws AbortionException {
        final List<IntegerConstraintRelation> workingCopy =
            IntegerConstraintCleaner.moveMaxesToFreshVars(constraints, fne);
        /*Right
         * Go through the list of constraints. If there is a max(a,b), try
         * to prove noMaxFilter(constraints) && a > b as UNSAT. Then replace
         * max by a <= b.
         */
        boolean changed = false;
        boolean changedAtAll = false;
        do {
            changedAtAll |= changed;
            changed = false;
            final Iterator<IntegerConstraintRelation> relIt = workingCopy.iterator();
            while (relIt.hasNext()) {
                final IntegerConstraintRelation rel = relIt.next();
                if (rel instanceof IntegerConstraintEQ && rel.getLeft().isVariable() && rel.getRight().isMax()) {
                    final IntegerConstraintVariable var = (IntegerConstraintVariable) rel.getLeft();
                    final IntegerConstraintMax max = (IntegerConstraintMax) rel.getRight();
                    final IntegerConstraintTerm maxLeft = max.getLeft();
                    final IntegerConstraintTerm maxRight = max.getRight();
                    final IntegerConstraintGT LeftBiggerRight = new IntegerConstraintGT(maxLeft, maxRight, false);
                    final IntegerConstraintGT RightBiggerLeft = new IntegerConstraintGT(maxRight, maxLeft, false);

                    try {
                        FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
                        List<TheoryAtom<SMTLIBTheoryAtom>> atoms =
                            IntegerConstraintCleaner.buildNoMaxFormula(workingCopy, factory);
                        for (final IntegerConstraintVariable v : max.getVariables()) {
                            atoms.add(
                                factory.buildTheoryAtom(
                                    new IntegerConstraintGE(v, new IntegerConstraintConstant(0), false).toSMTAtom()
                                )
                            );
                        }
                        atoms.add(factory.buildTheoryAtom(LeftBiggerRight.toSMTAtom()));
                        YicesEngine yicesEngine = new YicesEngine();
                        YNM res;
                        try {
                            res =
                                yicesEngine.satisfiable(
                                    Collections.singletonList(factory.buildAnd(atoms)),
                                    SMTLogic.QF_LIA,
                                    aborter
                                );
                        } catch (final WrongLogicException e) {
                            System.err.println("Yices error: " + e.getErrorMessage());
                            res = YNM.MAYBE;
                        }
                        //Yay, we can remove the MAX!
                        if (res == YNM.NO) {
                            relIt.remove();
                            workingCopy.add(new IntegerConstraintEQ(var, maxRight, false));
                            changed = true;
                            break;
                        }
                        factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
                        atoms = IntegerConstraintCleaner.buildNoMaxFormula(workingCopy, factory);
                        atoms.add(factory.buildTheoryAtom(RightBiggerLeft.toSMTAtom()));
                        yicesEngine = new YicesEngine();
                        try {
                            res =
                                yicesEngine.satisfiable(
                                    Collections.singletonList(factory.buildAnd(atoms)),
                                    SMTLogic.QF_LIA,
                                    aborter
                                );
                        } catch (final WrongLogicException e) {
                            System.err.println("Yices error: " + e.getErrorMessage());
                            res = YNM.MAYBE;
                        }
                        //Yay, we can remove the MAX!
                        if (res == YNM.NO) {
                            relIt.remove();
                            workingCopy.add(new IntegerConstraintEQ(var, maxLeft, false));
                            changed = true;
                            break;
                        }
                    } catch (final NotYetImplementedException e) {
                        //Not LIA-compatible. Ignore.
                    }
                }
            }
        } while (changed);
        constraints.clear();
        constraints.addAll(workingCopy);
        return changedAtAll;
    }

    private static boolean approximateMaxes(
        final List<IntegerConstraintRelation> constraints,
        final FreshNameGenerator fne,
        final Abortion aborter
    ) {
        final List<IntegerConstraintRelation> workingCopy =
            IntegerConstraintCleaner.moveMaxesToFreshVars(constraints, fne);
        final List<IntegerConstraintRelation> res = new LinkedList<IntegerConstraintRelation>();
        // Go through the list of constraints. If there is a max(a,b), replace it by a + b.
        boolean changed = false;
        for (final IntegerConstraintRelation rel : workingCopy) {
            if (rel instanceof IntegerConstraintEQ && rel.getLeft().isVariable() && rel.getRight().isMax()) {
                final IntegerConstraintVariable var = (IntegerConstraintVariable) rel.getLeft();
                final IntegerConstraintMax max = (IntegerConstraintMax) rel.getRight();
                final IntegerConstraintTerm maxLeft = max.getLeft();
                final IntegerConstraintTerm maxRight = max.getRight();
                res.add(new IntegerConstraintEQ(var, new IntegerConstraintAdd(maxLeft, maxRight), false));
                changed = true;
            } else {
                res.add(rel);
            }
        }
        constraints.clear();
        constraints.addAll(res);
        return changed;
    }

    private static List<TheoryAtom<SMTLIBTheoryAtom>> buildNoMaxFormula(
        final List<IntegerConstraintRelation> constraints,
        final FormulaFactory<SMTLIBTheoryAtom> factory
    ) {
        final List<TheoryAtom<SMTLIBTheoryAtom>> relFormulas = new LinkedList<TheoryAtom<SMTLIBTheoryAtom>>();
        for (final IntegerConstraintRelation rel : constraints) {
            if (!rel.containsMax()) {
                relFormulas.add(factory.buildTheoryAtom(rel.toSMTAtom()));
            }
        }
        return relFormulas;
    }

    private static TRSSubstitution createSubstitution(
        final IntegerConstraintVariable a,
        final IntegerConstraintTerm b
    ) {
        final TRSVariable from = TRSTerm.createVariable(a.getName());
        final TRSTerm to = b.toDPTerm();
        return TRSSubstitution.create(from, to);
    }

    private static IntegerConstraintTerm distributeMUL(
        final BinaryIntegerConstraintOperation leftOp,
        final IntegerConstraintTerm rightOp
    ) {
        final IntegerConstraintTerm leftLeftOp = leftOp.leftOp;
        final IntegerConstraintTerm leftRightOp = leftOp.rightOp;
        if (leftOp.isMul()) {
            if (leftLeftOp.isConstant() && rightOp.isConstant()) {
                return
                    leftOp.newInstance(
                        IntegerConstraintCleaner.simplifyTerm(new IntegerConstraintMul(leftLeftOp, rightOp), true),
                        leftRightOp
                    );
            } else if (leftRightOp.isConstant() && rightOp.isConstant()) {
                return
                    leftOp.newInstance(
                        IntegerConstraintCleaner.simplifyTerm(new IntegerConstraintMul(leftRightOp, rightOp), true),
                        leftLeftOp
                    );
            } else {
                return new IntegerConstraintMul(leftOp, rightOp);
            }
        } else {
            final IntegerConstraintTerm newOp =
                leftOp.newInstance(
                    IntegerConstraintCleaner.simplifyTerm(new IntegerConstraintMul(leftLeftOp, rightOp), true),
                    IntegerConstraintCleaner.simplifyTerm(new IntegerConstraintMul(leftRightOp, rightOp), true));
            return newOp;
        }
    }

    private static IntegerConstraintTerm funAppToTerm(final TRSFunctionApplication app, final FreshNameGenerator fne) {
        final FunctionSymbol sym = app.getRootSymbol();
        if (Globals.useAssertions) {
            IntegerConstraintCleaner.SYM_MAP.isPredefined(sym);
        }
        if (IntegerConstraintCleaner.SYM_MAP.isInt(sym, DomainFactory.INTEGERS)) {
            final BigInteger value = PredefinedSemanticsFactory.getIntValue(app, DomainFactory.INTEGERS);
            return new IntegerConstraintConstant(value);
        }

        if (IntegerConstraintCleaner.SYM_MAP.isUnaryMinus(sym)) {
            return new IntegerConstraintSub(new IntegerConstraintConstant(0), toTerm(app.getArgument(0), fne));
        }

        assert (app.getRootSymbol().getArity() == 2) : "Cannot convert term " + app;
        final IntegerConstraintTerm leftTerm = IntegerConstraintCleaner.toTerm(app.getArgument(0), fne);
        final IntegerConstraintTerm rightTerm = IntegerConstraintCleaner.toTerm(app.getArgument(1), fne);
        if (IntegerConstraintCleaner.SYM_MAP.isAdd(sym)) {
            return new IntegerConstraintAdd(leftTerm, rightTerm);
        } else if (IntegerConstraintCleaner.SYM_MAP.isSub(sym)) {
            if (rightTerm.isConstant()) {
                return
                    new IntegerConstraintAdd(
                        leftTerm,
                        new IntegerConstraintConstant(((IntegerConstraintConstant)rightTerm).value.negate())
                    );
            } else {
                return new IntegerConstraintSub(leftTerm, rightTerm);
            }
        } else if (IntegerConstraintCleaner.SYM_MAP.isMul(sym)) {
            return new IntegerConstraintMul(leftTerm, rightTerm);
        } else if (IntegerConstraintCleaner.SYM_MAP.isDiv(sym)) {
            return new IntegerConstraintDiv(leftTerm, rightTerm);
        } else if (IntegerConstraintCleaner.SYM_MAP.isMod(sym)) {
            return new IntegerConstraintMod(leftTerm, rightTerm);
        } else if (sym.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)) {
            return new IntegerConstraintMax(leftTerm, rightTerm);
        } else {
            throw new IllegalArgumentException(sym + " is not a legal operation.");
        }
    }

    private static IntegerConstraintRelation reduceConstants(final IntegerConstraintRelation rel) {
        final IntegerConstraintTerm left = rel.getLeft();
        final IntegerConstraintTerm right = rel.getRight();
        if (left instanceof IntegerConstraintConstant && right instanceof IntegerConstraintAdd) {
            final IntegerConstraintConstant c = (IntegerConstraintConstant) left;
            final IntegerConstraintAdd rightAdd = (IntegerConstraintAdd) right;
            // c REL c' + v
            if (rightAdd.getLeft() instanceof IntegerConstraintConstant) {
                final IntegerConstraintConstant cP = (IntegerConstraintConstant) rightAdd.getLeft();
                final IntegerConstraintTerm v = rightAdd.getRight();
                return
                    rel.newInstance(
                        new IntegerConstraintConstant(c.getValue().subtract(cP.getValue())),
                        v,
                        rel.isNegated()
                    );
            }
            // c REL v + c'
            if (rightAdd.getRight() instanceof IntegerConstraintConstant) {
                final IntegerConstraintConstant cP = (IntegerConstraintConstant) rightAdd.getRight();
                final IntegerConstraintTerm v = rightAdd.getLeft();
                return
                    rel.newInstance(
                        new IntegerConstraintConstant(c.getValue().subtract(cP.getValue())),
                        v,
                        rel.isNegated()
                    );
            }
        } else if (left instanceof IntegerConstraintConstant && right instanceof IntegerConstraintSub) {
            final IntegerConstraintConstant c = (IntegerConstraintConstant) left;
            final IntegerConstraintSub rightSub = (IntegerConstraintSub) right;
            // c REL c' - v
            if (rightSub.getLeft() instanceof IntegerConstraintConstant) {
                final IntegerConstraintConstant cP = (IntegerConstraintConstant) rightSub.getLeft();
                final IntegerConstraintTerm v = rightSub.getRight();
                return
                    rel.newInstance(
                        v,
                        new IntegerConstraintConstant(cP.getValue().subtract(c.getValue())),
                        rel.isNegated()
                    );
            }
            // c REL v - c'
            if (rightSub.getRight() instanceof IntegerConstraintConstant) {
                final IntegerConstraintConstant cP = (IntegerConstraintConstant) rightSub.getRight();
                final IntegerConstraintTerm v = rightSub.getLeft();
                return
                    rel.newInstance(new IntegerConstraintConstant(c.getValue().add(cP.getValue())), v, rel.isNegated());
            }
        }
        return rel;
    }

    /**��
     * @param rels sets of relations
     * @param subst old substitution
     * @return removes relations of the form "var = term" from <code>rels</code>
     *  and return the composition of <code>subst</code> and the corresponding
     *  substitutions.
     */
    private static TRSSubstitution splitOutSubstitutions(final List<IntegerConstraintRelation> rels) {
        TRSSubstitution res = TRSSubstitution.EMPTY_SUBSTITUTION;
        for (ListIterator<IntegerConstraintRelation> it = rels.listIterator(); it.hasNext();) {
            final IntegerConstraintRelation rel = it.next();
            if (rel instanceof IntegerConstraintEQ && !rel.containsMax()) {
                if (rel.getLeft().isVariable()) {
                    if (rel.getRight().getVariables().contains(rel.getLeft()) || rel.getRight().isDiv()) {
                        continue;
                    }
                    //if (rel.getLeft().isVariable() && rel.getRight().isConstant()) {
                    it.remove();
                    final IntegerConstraintVariable left = (IntegerConstraintVariable) rel.getLeft();
                    final IntegerConstraintTerm right = rel.getRight();
                    final TRSSubstitution relSubst = IntegerConstraintCleaner.createSubstitution(left, right);
                    res = res.compose(relSubst);
                    it = rels.listIterator();
                } else if (rel.getRight().isVariable()) {
                    //} else if (rel.getRight().isVariable() && rel.getLeft().isConstant()) {
                    if (rel.getLeft().getVariables().contains(rel.getRight()) || rel.getLeft().isDiv()) {
                        continue;
                    }
                    it.remove();
                    final IntegerConstraintVariable right = (IntegerConstraintVariable) rel.getRight();
                    final IntegerConstraintTerm left = rel.getLeft();
                    final TRSSubstitution relSubst = IntegerConstraintCleaner.createSubstitution(right, left);
                    res = res.compose(relSubst);
                    it = rels.listIterator();
                }
            }
        }
        return res;
    }

    private static IntegerConstraintRelation toRelation(TRSFunctionApplication app, final FreshNameGenerator fne) {
        boolean negated = false;
        if (IntegerConstraintCleaner.SYM_MAP.isLnot(app.getRootSymbol())) {
            negated = true;
            app = (TRSFunctionApplication)app.getArgument(0);
        }
        final FunctionSymbol sym = app.getRootSymbol();
        if (Globals.useAssertions) {
            assert (IntegerConstraintCleaner.SYM_MAP.isPredefined(sym));
        }
        if (IntegerConstraintCleaner.SYM_MAP.isBooleanTrue(sym)) {
            return new IntegerConstraintTRUE();
        } else if (IntegerConstraintCleaner.SYM_MAP.isBooleanFalse(sym)) {
            return new IntegerConstraintFALSE();
        }
        final IntegerConstraintTerm leftTerm = IntegerConstraintCleaner.toTerm(app.getArgument(0), fne);
        final IntegerConstraintTerm rightTerm = IntegerConstraintCleaner.toTerm(app.getArgument(1), fne);
        if (IntegerConstraintCleaner.SYM_MAP.isGe(sym)) {
            return new IntegerConstraintGE(leftTerm, rightTerm, negated);
        } else if (IntegerConstraintCleaner.SYM_MAP.isGt(sym)) {
            return new IntegerConstraintGT(leftTerm, rightTerm, negated);
        } else if (IntegerConstraintCleaner.SYM_MAP.isLe(sym)) {
            return new IntegerConstraintLE(leftTerm, rightTerm, negated);
        } else if (IntegerConstraintCleaner.SYM_MAP.isLt(sym)) {
            return new IntegerConstraintLT(leftTerm, rightTerm, negated);
        } else if (IntegerConstraintCleaner.SYM_MAP.isEq(sym)) {
            return new IntegerConstraintEQ(leftTerm, rightTerm, negated);
        } else if (IntegerConstraintCleaner.SYM_MAP.isNeq(sym)) {
            return new IntegerConstraintNE(leftTerm, rightTerm, negated);
        } else {
            throw new IllegalArgumentException(sym + " is not a legal relation.");
        }
    }

    private static IntegerConstraintTerm toTerm(final TRSTerm t, final FreshNameGenerator fne) {
        if (t instanceof TRSFunctionApplication) {
            return IntegerConstraintCleaner.funAppToTerm((TRSFunctionApplication) t, fne);
        } else {
            return IntegerConstraintCleaner.variableToTerm((TRSVariable) t, fne);
        }
    }

    private static IntegerConstraintTerm variableToTerm(final TRSVariable v, final FreshNameGenerator fne) {
        fne.lockName(v.getName());
        return new IntegerConstraintVariable(v.getName());
    }

    public static abstract class BinaryIntegerConstraintOperation extends IntegerConstraintTerm {

        private final IntegerConstraintTerm leftOp;

        private final IntegerConstraintTerm rightOp;

        public BinaryIntegerConstraintOperation(final IntegerConstraintTerm left, final IntegerConstraintTerm right) {
            this.leftOp = left;
            this.rightOp = right;
        }

        @Override
        public boolean containsMax() {
            return
                (this.getLeft().isMax() || this.getLeft().containsMax())
                || (this.getRight().isMax() || this.getRight().containsMax());
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (!(obj instanceof BinaryIntegerConstraintOperation)) {
                return false;
            }
            final BinaryIntegerConstraintOperation other = (BinaryIntegerConstraintOperation) obj;
            if (!this.operandString().equals(other.operandString())) {
                return false;
            }
            if (this.leftOp == null) {
                if (other.leftOp != null) {
                    return false;
                }
            } else if (!this.leftOp.equals(other.leftOp)) {
                return false;
            }
            if (this.rightOp == null) {
                if (other.rightOp != null) {
                    return false;
                }
            } else if (!this.rightOp.equals(other.rightOp)) {
                return false;
            }
            return true;
        }

        public IntegerConstraintTerm getLeft() {
            return this.leftOp;
        }

        public IntegerConstraintTerm getRight() {
            return this.rightOp;
        }

        @Override
        public void getVariables(final Collection<IntegerConstraintVariable> vars) {
            this.getLeft().getVariables(vars);
            this.getRight().getVariables(vars);
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((this.leftOp == null) ? 0 : this.leftOp.hashCode());
            result = prime * result + ((this.rightOp == null) ? 0 : this.rightOp.hashCode());
            result = prime * result + this.operandString().hashCode();
            return result;
        }

        public BinaryIntegerConstraintOperation newInstance(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right
        ) {
            try {
                return
                    this.getClass().getConstructor(
                        IntegerConstraintTerm.class,
                        IntegerConstraintTerm.class
                    ).newInstance(left, right);
            } catch (final IllegalArgumentException e) {
                throw new IllegalArgumentException(e);
            } catch (final SecurityException e) {
                throw new IllegalArgumentException(e);
            } catch (final InstantiationException e) {
                throw new IllegalArgumentException(e);
            } catch (final IllegalAccessException e) {
                throw new IllegalArgumentException(e);
            } catch (final InvocationTargetException e) {
                throw new IllegalArgumentException(e);
            } catch (final NoSuchMethodException e) {
                throw new IllegalArgumentException(e);
            }
        }

        @Override
        public IntegerConstraintTerm substitute(final IntegerConstraintVariable from, final IntegerConstraintTerm to) {
            final IntegerConstraintTerm leftSubst = this.leftOp.substitute(from, to);
            final IntegerConstraintTerm rightSubst = this.rightOp.substitute(from, to);
            if (leftSubst == this.leftOp && rightSubst == this.rightOp) {
                return this;
            } else {
                return this.newInstance(leftSubst, rightSubst);
            }
        }

        @Override
        public void toClauseString(final StringBuilder sb) {
            sb.append("(");
            this.getLeft().toClauseString(sb);
            sb.append(" ").append(this.operandString()).append(" ");
            this.getRight().toClauseString(sb);
            sb.append(")");
        }

        @Override
        public TRSTerm toDPTerm() {
            final TRSTerm left = this.getLeft().toDPTerm();
            final TRSTerm right = this.getRight().toDPTerm();
            return
                TRSTerm.createFunctionApplication(
                    IntegerConstraintCleaner.SYM_MAP.getSym(this.operationFunc(), DomainFactory.INTEGER_INTEGER),
                    left,
                    right
                );
        }

        @Override
        public SMTLIBIntValue toSMTIntValue() {
            throw
                new NotYetImplementedException(
                    "We only support SMT-LIA, so cannot export " + this.toString() + " to SMT"
                );
        }

        @Override
        public String toString() {
            return this.getLeft() + " " + this.operandString() + " " + this.getRight();
        }

        abstract String operandString();

        abstract Func operationFunc();

    }

    public static final class IntegerConstraintAdd extends BinaryIntegerConstraintOperation {

        public IntegerConstraintAdd(final IntegerConstraintTerm left, final IntegerConstraintTerm right) {
            super(left, right);
        }

        @Override
        public TRSTerm toDPTerm() {
            final IntegerConstraintTerm right = this.getRight();
            if (right.isConstant() && ((IntegerConstraintConstant) right).value.signum() < 0) {
                return
                    new IntegerConstraintSub(
                        this.getLeft(),
                        new IntegerConstraintConstant(((IntegerConstraintConstant) right).value.negate())
                    ).toDPTerm();
            }
            return super.toDPTerm();
        }

        @Override
        public SMTLIBIntValue toSMTIntValue() {
            final List<SMTLIBIntValue> operands = new LinkedList<SMTLIBIntValue>();
            operands.add(this.getLeft().toSMTIntValue());
            operands.add(this.getRight().toSMTIntValue());
            return SMTLIBIntPlus.create(operands);
        }

        @Override
        String operandString() {
            return "+";
        }

        @Override
        Func operationFunc() {
            return Func.Add;
        }

    }

    public static final class IntegerConstraintConstant
    extends IntegerConstraintTerm implements Comparable<IntegerConstraintConstant> {

        final BigInteger value;

        public IntegerConstraintConstant(final BigInteger v) {
            this.value = v;
        }

        public IntegerConstraintConstant(final int v) {
            this.value = BigInteger.valueOf(v);
        }

        public IntegerConstraintConstant(final long v) {
            this.value = BigInteger.valueOf(v);
        }

        @Override
        public int compareTo(final IntegerConstraintConstant that) {
            return this.value.compareTo(that.value);
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            final IntegerConstraintConstant other = (IntegerConstraintConstant) obj;
            if (!this.value.equals(other.value)) {
                return false;
            }
            return true;
        }

        public BigInteger getValue() {
            return this.value;
        }

        @Override
        public void getVariables(final Collection<IntegerConstraintVariable> vars) {
            //Do nothing
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + this.value.hashCode();
            return result;
        }

        @Override
        public IntegerConstraintTerm substitute(final IntegerConstraintVariable from, final IntegerConstraintTerm to) {
            return this;
        }

        @Override
        public void toClauseString(final StringBuilder sb) {
            sb.append(this.value.toString());
        }

        @Override
        public TRSTerm toDPTerm() {
            return IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.create(this.value), DomainFactory.INTEGERS);
        }

        @Override
        public SMTLIBIntValue toSMTIntValue() {
            return SMTLIBIntConstant.create(this.value);
        }

        @Override
        public String toString() {
            return this.value.toString();
        }

    }

    public static final class IntegerConstraintDiv extends BinaryIntegerConstraintOperation {

        public IntegerConstraintDiv(final IntegerConstraintTerm left, final IntegerConstraintTerm right) {
            super(left, right);
        }

        @Override
        String operandString() {
            return "/";
        }

        @Override
        Func operationFunc() {
            return Func.Div;
        }

    }

    public static final class IntegerConstraintEQ extends IntegerConstraintRelation {

        public IntegerConstraintEQ(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            super(left, right, negated);
        }

        @Override
        public IntegerConstraintRelation invert() {
            return new IntegerConstraintEQ(this.getRight(), this.getLeft(), this.isNegated());
        }

        @Override
        public IntegerConstraintRelation switchNegation() {
            return new IntegerConstraintNE(this.getLeft(), this.getRight(), !this.isNegated());
        }

        @Override
        public SMTLIBTheoryAtom toSMTAtom() {
            return SMTLIBIntEquals.create(this.getLeft().toSMTIntValue(), this.getRight().toSMTIntValue());
        }

        @Override
        String operandString() {
            return "=";
        }

        @Override
        Func relationFunc() {
            return Func.Eq;
        }

    }

    //Pseudo-class signifying FALSE
    public static final class IntegerConstraintFALSE extends IntegerConstraintRelation {

        public IntegerConstraintFALSE() {
            super(new IntegerConstraintConstant(0), new IntegerConstraintConstant(1), false);
        }

        public IntegerConstraintFALSE(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            super(new IntegerConstraintConstant(0), new IntegerConstraintConstant(1), false);
        }

        @Override
        public IntegerConstraintRelation invert() {
            return this;
        }

        @Override
        public IntegerConstraintRelation switchNegation() {
            return new IntegerConstraintFALSE(new IntegerConstraintConstant(0), new IntegerConstraintConstant(1), false);
        }

        @Override
        public TRSFunctionApplication toDPTerm() {
            return TRSTerm
                .createFunctionApplication(IntegerConstraintCleaner.SYM_MAP.getBooleanFalse().getSym());
        }

        @Override
        public SMTLIBTheoryAtom toSMTAtom() {
            return SMTLIBBoolFalse.create();
        }

        @Override
        String operandString() {
            return "=";
        }

        @Override
        Func relationFunc() {
            return Func.Eq;
        }

    }

    public static final class IntegerConstraintGE extends IntegerConstraintRelation {

        public IntegerConstraintGE(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            super(left, right, negated);
        }

        @Override
        public IntegerConstraintRelation invert() {
            return new IntegerConstraintLE(this.getRight(), this.getLeft(), this.isNegated());
        }

        @Override
        public IntegerConstraintRelation switchNegation() {
            return new IntegerConstraintLT(this.getLeft(), this.getRight(), !this.isNegated());
        }

        @Override
        public TRSFunctionApplication toDPTerm() {
            if (this.getRight().isConstant() && this.getLeft().isVariable()) {
                final TRSTerm right = this.getRight().toDPTerm();
                return
                    TRSTerm.createFunctionApplication(
                        IntegerConstraintCleaner.SYM_MAP.getSym(Func.Gt, DomainFactory.INTEGER_INTEGER),
                        new IntegerConstraintAdd(this.getLeft(), new IntegerConstraintConstant(1)).toDPTerm(),
                        right
                    );
            }
            return super.toDPTerm();
        }

        @Override
        public SMTLIBTheoryAtom toSMTAtom() {
            return SMTLIBIntGE.create(this.getLeft().toSMTIntValue(), this.getRight().toSMTIntValue());
        }

        @Override
        String operandString() {
            return ">=";
        }

        @Override
        Func relationFunc() {
            return Func.Ge;
        }

    }

    public static final class IntegerConstraintGT extends IntegerConstraintRelation {

        public IntegerConstraintGT(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            super(left, right, negated);
        }

        @Override
        public IntegerConstraintRelation invert() {
            return new IntegerConstraintLT(this.getRight(), this.getLeft(), this.isNegated());
        }

        @Override
        public IntegerConstraintRelation switchNegation() {
            return new IntegerConstraintLE(this.getLeft(), this.getRight(), !this.isNegated());
        }

        @Override
        public SMTLIBTheoryAtom toSMTAtom() {
            return SMTLIBIntGT.create(this.getLeft().toSMTIntValue(), this.getRight().toSMTIntValue());
        }

        @Override
        String operandString() {
            return ">";
        }

        @Override
        Func relationFunc() {
            return Func.Gt;
        }

    }

    public static final class IntegerConstraintLE extends IntegerConstraintRelation {

        public IntegerConstraintLE(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            super(left, right, negated);
        }

        @Override
        public IntegerConstraintRelation invert() {
            return new IntegerConstraintGE(this.getRight(), this.getLeft(), this.isNegated());
        }

        @Override
        public IntegerConstraintRelation switchNegation() {
            return new IntegerConstraintGT(this.getLeft(), this.getRight(), !this.isNegated());
        }

        @Override
        public void toClauseString(final StringBuilder sb) {
            if (this.isNegated()) {
                this.getLeft().toClauseString(sb);
                sb.append(" >= ");
                this.getRight().toClauseString(sb);
            } else {
                this.getLeft().toClauseString(sb);
                sb.append(" =< ");
                this.getRight().toClauseString(sb);
            }
        }

        @Override
        public TRSFunctionApplication toDPTerm() {
            if (this.getLeft().isConstant() && this.getRight().isVariable()) {
                final TRSTerm left = this.getLeft().toDPTerm();
                return TRSTerm.createFunctionApplication(
                    IntegerConstraintCleaner.SYM_MAP.getSym(Func.Gt, DomainFactory.INTEGER_INTEGER),
                    left,
                    new IntegerConstraintAdd(this.getRight(), new IntegerConstraintConstant(1)).toDPTerm());
            }
            return super.toDPTerm();
        }

        @Override
        public SMTLIBTheoryAtom toSMTAtom() {
            return SMTLIBIntLE.create(this.getLeft().toSMTIntValue(), this.getRight().toSMTIntValue());
        }

        @Override
        String operandString() {
            return "<=";
        }

        @Override
        Func relationFunc() {
            return Func.Le;
        }

    }

    public static final class IntegerConstraintLT extends IntegerConstraintRelation {

        public IntegerConstraintLT(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            super(left, right, negated);
        }

        @Override
        public IntegerConstraintRelation invert() {
            return new IntegerConstraintGT(this.getRight(), this.getLeft(), this.isNegated());
        }

        @Override
        public IntegerConstraintRelation switchNegation() {
            return new IntegerConstraintGE(this.getLeft(), this.getRight(), !this.isNegated());
        }

        @Override
        public SMTLIBTheoryAtom toSMTAtom() {
            return SMTLIBIntLT.create(this.getLeft().toSMTIntValue(), this.getRight().toSMTIntValue());
        }

        @Override
        String operandString() {
            return "<";
        }

        @Override
        Func relationFunc() {
            return Func.Lt;
        }

    }

    public static final class IntegerConstraintMax extends BinaryIntegerConstraintOperation {

        public IntegerConstraintMax(final IntegerConstraintTerm left, final IntegerConstraintTerm right) {
            super(left, right);
        }

        @Override
        public TRSTerm toDPTerm() {
            final TRSTerm left = this.getLeft().toDPTerm();
            final TRSTerm right = this.getRight().toDPTerm();
            return TRSTerm.createFunctionApplication(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL, left, right);
        }

        @Override
        public String toString() {
            return "max(" + this.getLeft() + "," + this.getRight() + ")";
        }

        @Override
        String operandString() {
            return "max";
        }

        @Override
        Func operationFunc() {
            throw new NotYetImplementedException("This doesn't make sense for max");
        }

    }

    public static final class IntegerConstraintMod extends BinaryIntegerConstraintOperation {

        public IntegerConstraintMod(final IntegerConstraintTerm left, final IntegerConstraintTerm right) {
            super(left, right);
        }

        @Override
        String operandString() {
            return "%";
        }

        @Override
        Func operationFunc() {
            return Func.Mod;
        }

    }

    public static final class IntegerConstraintMul extends BinaryIntegerConstraintOperation {

        public IntegerConstraintMul(final IntegerConstraintTerm left, final IntegerConstraintTerm right) {
            super(left, right);
        }

        @Override
        public SMTLIBIntValue toSMTIntValue() {
            final List<SMTLIBIntValue> operands = new LinkedList<SMTLIBIntValue>();
            operands.add(this.getLeft().toSMTIntValue());
            operands.add(this.getRight().toSMTIntValue());
            if (!this.getLeft().isConstant() && !this.getRight().isConstant()) {
                throw
                    new NotYetImplementedException(
                        "We only support SMT-LIA, so cannot export " + this.toString() + " to SMT"
                    );
            }
            return SMTLIBIntMult.create(operands);
        }

        @Override
        String operandString() {
            return "*";
        }

        @Override
        Func operationFunc() {
            return Func.Mul;
        }
    }

    public static final class IntegerConstraintNE extends IntegerConstraintRelation {

        public IntegerConstraintNE(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            super(left, right, negated);
        }

        @Override
        public IntegerConstraintRelation invert() {
            return this;
        }

        @Override
        public IntegerConstraintRelation switchNegation() {
            return new IntegerConstraintEQ(this.getLeft(), this.getRight(), !this.isNegated());
        }

        @Override
        public void toClauseString(final StringBuilder sb) {
            if (this.isNegated()) {
                new IntegerConstraintEQ(this.getLeft(), this.getRight(), false).toClauseString(sb);
            } else {
                sb.append("\\+(");
                new IntegerConstraintEQ(this.getLeft(), this.getRight(), false).toClauseString(sb);
                sb.append(")");
            }
        }

        @Override
        public TRSFunctionApplication toDPTerm() {
            return this.switchNegation().toDPTerm();
        }

        @Override
        public SMTLIBTheoryAtom toSMTAtom() {
            return SMTLIBIntUnequal.create(this.getLeft().toSMTIntValue(), this.getRight().toSMTIntValue());
        }

        @Override
        String operandString() {
            return "!=";
        }

        @Override
        Func relationFunc() {
            return Func.Neq;
        }

    }

    public static abstract class IntegerConstraintRelation implements Comparable<IntegerConstraintRelation> {

        private final IntegerConstraintTerm left;

        private final boolean negated;

        private final IntegerConstraintTerm right;

        public IntegerConstraintRelation(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            this.negated = negated;
            this.left = left;
            this.right = right;
        }

        public IntegerConstraintRelation canonicalize() {
            if (this.getLeft().toString().compareTo(this.getRight().toString()) < 0) {
                return this.invert();
            }
            return this;
        }

        @Override
        public int compareTo(final IntegerConstraintRelation other) {
            return this.toString().compareTo(other.toString());
        }

        public boolean containsMax() {
            return
                this.getLeft().isMax()
                || this.getLeft().containsMax()
                || this.getRight().isMax()
                || this.getRight().containsMax();
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (!(obj instanceof IntegerConstraintRelation)) {
                return false;
            }
            final IntegerConstraintRelation other = (IntegerConstraintRelation)obj;
            if (this.left == null) {
                if (other.left != null) {
                    return false;
                }
            } else if (!this.left.equals(other.left)) {
                return false;
            }
            if (this.negated != other.negated) {
                return false;
            }
            if (this.right == null) {
                if (other.right != null) {
                    return false;
                }
            } else if (!this.right.equals(other.right)) {
                return false;
            }
            if (!this.operandString().equals(other.operandString())) {
                return false;
            }
            return true;
        }

        final public IntegerConstraintTerm getLeft() {
            return this.left;
        }

        final public IntegerConstraintTerm getRight() {
            return this.right;
        }

        public Collection<IntegerConstraintVariable> getVariables() {
            final LinkedHashSet<IntegerConstraintVariable> res = new LinkedHashSet<IntegerConstraintVariable>();
            this.getVariables(res);
            return res;
        }

        public void getVariables(final Collection<IntegerConstraintVariable> vars) {
            this.getLeft().getVariables(vars);
            this.getRight().getVariables(vars);
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((this.left == null) ? 0 : this.left.hashCode());
            result = prime * result + (this.negated ? 1231 : 1237);
            result = prime * result + ((this.right == null) ? 0 : this.right.hashCode());
            result = prime * result + this.operandString().hashCode();
            return result;
        }

        public boolean isNegated() {
            return this.negated;
        }

        final public IntegerConstraintRelation newInstance(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            try {
                return
                    this.getClass().getConstructor(
                        IntegerConstraintTerm.class,
                        IntegerConstraintTerm.class,
                        Boolean.TYPE
                    ).newInstance(
                        left,
                        right,
                        negated
                    );
            } catch (final IllegalArgumentException e) {
                throw new IllegalArgumentException(e);
            } catch (final SecurityException e) {
                throw new IllegalArgumentException(e);
            } catch (final InstantiationException e) {
                throw new IllegalArgumentException(e);
            } catch (final IllegalAccessException e) {
                throw new IllegalArgumentException(e);
            } catch (final InvocationTargetException e) {
                throw new IllegalArgumentException(e);
            } catch (final NoSuchMethodException e) {
                throw new IllegalArgumentException(e);
            }
        }

        public IntegerConstraintRelation normalize() {
            if (this.isNegated()) {
                return this.switchNegation();
            } else {
                return this;
            }
        }

        final public IntegerConstraintRelation substitute(
            final IntegerConstraintVariable a,
            final IntegerConstraintTerm b
        ) {
            return this.newInstance(this.left.substitute(a, b), this.right.substitute(a, b), this.negated);
        }

        public void toClauseString(final StringBuilder sb) {
            if (this.isNegated()) {
                sb.append("\\+(");
                this.switchNegation().toClauseString(sb);
                sb.append(")");
            } else {
                this.getLeft().toClauseString(sb);
                sb.append(" ").append(this.operandString()).append(" ");
                this.getRight().toClauseString(sb);
            }
        }

        public TRSFunctionApplication toDPTerm() {
            final TRSTerm left = this.getLeft().toDPTerm();
            final TRSTerm right = this.getRight().toDPTerm();
            TRSFunctionApplication relation =
                TRSTerm.createFunctionApplication(
                    IntegerConstraintCleaner.SYM_MAP.getSym(this.relationFunc(), DomainFactory.INTEGER_INTEGER),
                    left,
                    right
                );
            if (this.isNegated()) {
                relation =
                    TRSTerm.createFunctionApplication(
                        IntegerConstraintCleaner.SYM_MAP.getSym(Func.Lnot, DomainFactory.BOOLEAN),
                        relation
                    );
            }
            return relation;
        }

        public abstract SMTLIBTheoryAtom toSMTAtom();

        @Override
        public String toString() {
            return this.left.toString() + " " + this.operandString() + " " + this.right.toString();
        }

        abstract IntegerConstraintRelation invert();

        abstract String operandString();

        abstract Func relationFunc();

        abstract IntegerConstraintRelation switchNegation();

    }

    public static final class IntegerConstraintSub extends BinaryIntegerConstraintOperation {

        public IntegerConstraintSub(final IntegerConstraintTerm left, final IntegerConstraintTerm right) {
            super(left, right);
        }

        @Override
        public SMTLIBIntValue toSMTIntValue() {
            final List<SMTLIBIntValue> operands = new LinkedList<SMTLIBIntValue>();
            operands.add(this.getLeft().toSMTIntValue());
            operands.add(this.getRight().toSMTIntValue());
            return SMTLIBIntMinus.create(operands);
        }

        @Override
        String operandString() {
            return "-";
        }

        @Override
        Func operationFunc() {
            return Func.Sub;
        }

    }

    /**
     * Basic class for terms. These terms are intended as an internal representation of integer constraints.
     * @author christian
     */
    public static abstract class IntegerConstraintTerm {

        public boolean containsMax() {
            return false;
        }

        public Collection<IntegerConstraintVariable> getVariables() {
            final LinkedHashSet<IntegerConstraintVariable> res = new LinkedHashSet<IntegerConstraintVariable>();
            this.getVariables(res);
            return res;
        }

        public abstract void getVariables(Collection<IntegerConstraintVariable> vars);

        public boolean isAdd() {
            return this instanceof IntegerConstraintAdd;
        }

        public boolean isAtom() {
            return this instanceof IntegerConstraintConstant || this instanceof IntegerConstraintVariable;
        }

        public boolean isConstant() {
            return this instanceof IntegerConstraintConstant;
        }

        public boolean isDiv() {
            return this instanceof IntegerConstraintDiv;
        }

        public boolean isMax() {
            return this instanceof IntegerConstraintMax;
        }

        public boolean isMod() {
            return this instanceof IntegerConstraintMod;
        }

        public boolean isMul() {
            return this instanceof IntegerConstraintMul;
        }

        public boolean isSub() {
            return this instanceof IntegerConstraintSub;
        }

        public boolean isVariable() {
            return (this instanceof IntegerConstraintVariable);
        }

        public abstract IntegerConstraintTerm substitute(IntegerConstraintVariable from, IntegerConstraintTerm to);

        public abstract void toClauseString(StringBuilder sb);

        public abstract TRSTerm toDPTerm();

        public abstract SMTLIBIntValue toSMTIntValue();

    }

    //Pseudo-class signifying TRUE
    public static final class IntegerConstraintTRUE extends IntegerConstraintRelation {

        public IntegerConstraintTRUE() {
            super(new IntegerConstraintConstant(0), new IntegerConstraintConstant(0), false);
        }

        public IntegerConstraintTRUE(
            final IntegerConstraintTerm left,
            final IntegerConstraintTerm right,
            final boolean negated
        ) {
            super(new IntegerConstraintConstant(0), new IntegerConstraintConstant(0), false);
        }

        @Override
        public IntegerConstraintRelation invert() {
            return this;
        }

        @Override
        public IntegerConstraintRelation switchNegation() {
            return new IntegerConstraintTRUE();
        }

        @Override
        public TRSFunctionApplication toDPTerm() {
            return TRSTerm.createFunctionApplication(IntegerConstraintCleaner.SYM_MAP.getBooleanTrue().getSym());
        }

        @Override
        public SMTLIBTheoryAtom toSMTAtom() {
            return SMTLIBBoolTrue.create();
        }

        @Override
        String operandString() {
            return "=";
        }

        @Override
        Func relationFunc() {
            return Func.Eq;
        }

    }

    public static final class IntegerConstraintVariable extends IntegerConstraintTerm {

        final private String name;

        public IntegerConstraintVariable(final String name) {
            this.name = name;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }
            final IntegerConstraintVariable other = (IntegerConstraintVariable)obj;
            if (this.name == null) {
                if (other.name != null) {
                    return false;
                }
            } else if (!this.name.equals(other.name)) {
                return false;
            }
            return true;
        }

        public String getName() {
            return this.name;
        }

        @Override
        public void getVariables(final Collection<IntegerConstraintVariable> vars) {
            vars.add(this);
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((this.name == null) ? 0 : this.name.hashCode());
            return result;
        }

        @Override
        public IntegerConstraintTerm substitute(final IntegerConstraintVariable from, final IntegerConstraintTerm to) {
            if (this.name == from.name) {
                return to;
            } else {
                return this;
            }
        }

        @Override
        public void toClauseString(final StringBuilder sb) {
            sb.append(this.name);
        }

        @Override
        public TRSTerm toDPTerm() {
            return TRSTerm.createVariable(this.name);
        }

        @Override
        public SMTLIBIntValue toSMTIntValue() {
            return SMTLIBIntVariable.create(this.name);
        }

        @Override
        public String toString() {
            return this.name;
        }
    }

}
