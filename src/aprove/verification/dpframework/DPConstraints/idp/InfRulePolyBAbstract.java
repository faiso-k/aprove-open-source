/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.idp.InfRuleSMT.VarAnalysis.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class InfRulePolyBAbstract extends InfRuleSMT {

    protected static final boolean LINEAR_SPLIT = true;
    protected static final boolean SPLIT_CEIL = true;

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        final Constraint res = this.processImpl(implication, aborter);
        return (res == null ? null : new Pair<Constraint, InfProofStepInfo>(res, null));
    }

    protected Constraint processImpl(final Implication implication, final Abortion aborter) throws AbortionException {
        // System.out.println("processImpl " + implication);
        final IDPGInterpretation interpretation = (IDPGInterpretation) this.getIrc().getPolyInterpretation();
        final Triple<Boolean, Map<GPolyVar, VarAnalysis>, Set<Set<MonomialAnalysis>>> analysis =
            this.analyzeImpl(implication, interpretation, aborter);
        if (analysis.x) {
            // contradiction
            return ConstraintSet.emptySet;
        }
        if (((IDPGInterpretation) this.irc.getPolyInterpretation()).isNat()) {
            return implication;
        }

        return this.buildConstraint(implication, interpretation, analysis.y, analysis.z, aborter);
    }

    protected Constraint buildConstraint(
        final Implication implication,
        final GInterpretation<BigIntImmutable> interpretation,
        final Map<GPolyVar, VarAnalysis> varAnalysis,
        final Set<Set<MonomialAnalysis>> usable,
        final Abortion aborter) throws AbortionException
    {
        boolean hasUnboundedVar = false;
        Set<GPolyVar> conclusionVariables = implication.getConclusion().getPolyVariables();
        for (final VarAnalysis analysis : varAnalysis.values()) {
            final Signum sign = analysis.getSign();
            if (sign.getId() == null) {
                hasUnboundedVar = true;
            }
            if (sign == Signum.Contradiction) {
                // System.err.println("Contradiction in " + analysis.getVar());
                return ConstraintSet.emptySet;
            }
            if (sign == Signum.Zero) {
                // System.err.println("Zero Promotion");
                final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory =
                    interpretation.getFactory().getFactory();
                final Set<Constraint> conditionsLEQ =
                    this.replacePolyVar(
                        interpretation,
                        factory,
                        analysis.getVar(),
                        factory.zero(),
                        implication.getConditions(),
                        null);

                Set<Constraint> newLEQConclusion;
                if (implication.getConclusion().isConstraintSet()) {
                    newLEQConclusion =
                        this.replacePolyVar(
                            interpretation,
                            factory,
                            analysis.getVar(),
                            factory.zero(),
                            (ConstraintSet) implication.getConclusion(),
                            null);
                } else {
                    newLEQConclusion =
                        this.replacePolyVar(
                            interpretation,
                            factory,
                            analysis.getVar(),
                            factory.zero(),
                            ConstraintSet.flatCreate(implication.getConclusion()),
                            null);
                }
                // System.err.println("Promote Zero" + analysis.getVar());
                return Implication.create(
                    implication.getId(),
                    implication.getQuantor(),
                    ConstraintSet.create(conditionsLEQ),
                    ConstraintSet.create(newLEQConclusion),
                    implication.getData());
            }
            if (InfRulePolyBAbstract.LINEAR_SPLIT
                && (sign.getId() == null || sign.isStrict())
                && (conclusionVariables == null || conclusionVariables.contains(analysis.getVar())))
            {
                final Set<MonomialSplit> splits = analysis.getSolvingConstraints();
                final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory =
                    interpretation.getFactory().getFactory();
                final GPolyFactory<BigIntImmutable, GPolyVar> innerFactory =
                    interpretation.getFactory().getInnerFactory();
                outerSplit: for (final MonomialSplit split : splits) {
                    if (aborter != null) {
                        aborter.checkAbortion();
                    }
                    if (split.getSolving().size() == 1) {
                        final MonomialAnalysis solvingAna = split.getSolving().iterator().next();
                        final GPoly<BigIntImmutable, GPolyVar> solvingCoeff = solvingAna.getCoeff();
                        if (!solvingCoeff.isFlat(interpretation.getInnerRingMonoid())) {
                            interpretation.getFvInner().applyTo(solvingCoeff);
                        }
                        if (solvingCoeff.isConstant()) {
                            final BigIntImmutable coeffValue =
                                solvingCoeff.getConstantPart(interpretation.getInnerRingMonoid());
                            GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> replacement = null;
                            for (final MonomialAnalysis neededAna : split.getNeeded()) {
                                final GPoly<BigIntImmutable, GPolyVar> neededCoeff = neededAna.getCoeff();
                                if (!neededCoeff.isFlat(interpretation.getInnerRingMonoid())) {
                                    interpretation.getFvInner().applyTo(neededCoeff);
                                }
                                boolean splitUsable = false;
                                boolean divHasRemainder = false;
                                BigIntImmutable neededValue = null;
                                if (neededCoeff.isConstant()) {
                                    neededValue = neededCoeff.getConstantPart(interpretation.getInnerRingMonoid());
                                    if (neededValue.getBigInt().mod(coeffValue.getBigInt().abs()).signum() == 0) {
                                        splitUsable = true;
                                    } else if (neededAna.getVariables().isEmpty() && InfRulePolyBAbstract.SPLIT_CEIL) {
                                        splitUsable = true;
                                        divHasRemainder = true;
                                    }
                                }
                                if (!splitUsable) {
                                    continue outerSplit;
                                }
                                final Collection<GPolyVar> vars = new ArrayList<GPolyVar>();
                                for (final Map.Entry<GPolyVar, BigInteger> varEntry : neededAna
                                    .getMonomial()
                                    .getExponents()
                                    .entrySet())
                                {
                                    final GPolyVar var = varEntry.getKey();
                                    for (int i = varEntry.getValue().intValue() - 1; i >= 0; i--) {
                                        vars.add(var);
                                    }
                                }
                                BigIntImmutable newCoeff;
                                if (divHasRemainder) {
                                    if (coeffValue.getBigInt().signum() > 0) {
                                        // ceil
                                        newCoeff =
                                            BigIntImmutable.create(neededValue
                                                .getBigInt()
                                                .divide(coeffValue.getBigInt())
                                                .add(BigInteger.ONE)
                                                .negate());
                                    } else {
                                        // floor
                                        newCoeff =
                                            BigIntImmutable.create(neededValue
                                                .getBigInt()
                                                .divide(coeffValue.getBigInt())
                                                .subtract(BigInteger.ONE)
                                                .negate());
                                    }
                                } else {
                                    newCoeff =
                                        BigIntImmutable.create(neededValue
                                            .getBigInt()
                                            .divide(coeffValue.getBigInt())
                                            .negate());
                                }
                                final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> mon =
                                    factory.concat(innerFactory.buildFromCoeff(newCoeff), factory.buildVariables(vars));
                                if (replacement == null) {
                                    replacement = mon;
                                } else {
                                    replacement = factory.plus(replacement, mon);
                                }
                            }
                            if (replacement != null) {
                                if (coeffValue.getBigInt().signum() >= 0) {
                                    replacement =
                                        factory.plus(replacement, factory.buildFromVariable(analysis.getVar()));
                                } else {
                                    replacement =
                                        factory.minus(replacement, factory.buildFromVariable(analysis.getVar()));
                                }
                                interpretation.getFvOuter().applyTo(replacement);
                                // System.err.println(interpretation.getFactory().wrap(replacement).exportFlatDeep(interpretation.getFvInner(), interpretation.getFvOuter(), new PLAIN_Util()));

                                // System.err.println("LinSplit " + analysis.getVar() + " by " + replacement + "( " + split.constraint + ")");
                                Set<Constraint> newConditions =
                                    new LinkedHashSet<Constraint>(implication.getConditions());
                                newConditions.remove(split.constraint);
                                newConditions =
                                    this.replacePolyVar(
                                        interpretation,
                                        factory,
                                        analysis.getVar(),
                                        replacement,
                                        implication.getConditions(),
                                        null);

//                                newConditions.add(PolyAtom.<BigIntImmutable>create(factory.buildFromVariable(analysis.getVar()), ConstraintType.GE, interpretation, null, null, null, -1));

                                Set<Constraint> newConclusion;
                                if (implication.getConclusion().isConstraintSet()) {
                                    newConclusion =
                                        this.replacePolyVar(
                                            interpretation,
                                            factory,
                                            analysis.getVar(),
                                            replacement,
                                            (ConstraintSet) implication.getConclusion(),
                                            null);
                                } else {
                                    newConclusion =
                                        this.replacePolyVar(
                                            interpretation,
                                            factory,
                                            analysis.getVar(),
                                            replacement,
                                            ConstraintSet.flatCreate(implication.getConclusion()),
                                            null);
                                }
                                return Implication.create(
                                    implication.getId(),
                                    implication.getQuantor(),
                                    ConstraintSet.create(newConditions),
                                    ConstraintSet.create(newConclusion),
                                    implication.getData());
                            }
                        }
                    }
                }
            }
            if (sign == Signum.Neg || sign == Signum.StrictNeg) {
                // System.err.println("SPLIT NEGATIVE " + analysis.getVar());
                final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory =
                    interpretation.getFactory().getFactory();
                final Set<Constraint> conditionsLEQ =
                    this.buildConstraitsLEQ(interpretation, factory, analysis.getVar(), implication.getConditions(), null);

                Set<Constraint> newLEQConclusion;
                if (implication.getConclusion().isConstraintSet()) {
                    newLEQConclusion =
                        this.buildConstraitsLEQ(
                            interpretation,
                            factory,
                            analysis.getVar(),
                            (ConstraintSet) implication.getConclusion(),
                            null);
                } else {
                    newLEQConclusion =
                        this.buildConstraitsLEQ(
                            interpretation,
                            factory,
                            analysis.getVar(),
                            ConstraintSet.flatCreate(implication.getConclusion()),
                            null);
                }
                return Implication.create(
                    implication.getId(),
                    implication.getQuantor(),
                    ConstraintSet.create(conditionsLEQ),
                    ConstraintSet.create(newLEQConclusion),
                    implication.getData());
            }
        }
        if (!hasUnboundedVar) {
            return implication;
        }

        final GPolyVar nextSplit =
            this.decideNextSplit(implication, interpretation, varAnalysis, usable, conclusionVariables);
        if (nextSplit != null) {
            conclusionVariables = null;
            /*
            conclusionVariables = new HashSet<GPolyVar>(conclusionVariables);
            for (Constraint condition : implication.getConditions()) {
                Set<GPolyVar> constraintVars = condition.getPolyVariables();
                if (containsAny(constraintVars, conclusionVariables)) {
                    conclusionVariables.addAll(constraintVars);
                }
            }*/
        }
        if (nextSplit == null
            && (conclusionVariables == null || conclusionVariables.containsAll(implication
                .getConditions()
                .getPolyVariables())))
        {
            // nothing to do
            return null;
        }
        final Set<Constraint> res = new LinkedHashSet<Constraint>();
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory =
            interpretation.getFactory().getFactory();
        // System.err.println("SPLIT " + nextSplit);

        // x >= 0
        final Set<Constraint> conditionsGEQ = new LinkedHashSet<Constraint>();
        for (final Constraint condition : implication.getConditions()) {
            if (conclusionVariables == null || conclusionVariables.containsAll(condition.getPolyVariables())) {
                conditionsGEQ.add(condition);
            }
        }
        if (nextSplit != null) {
            conditionsGEQ.add(PolyAtom.<BigIntImmutable>create(
                factory.buildFromVariable(nextSplit),
                ConstraintType.GE,
                interpretation,
                null,
                null,
                null,
                -1));
        }
        final Implication implGEQ =
            Implication.create(
                implication.getId(),
                implication.getQuantor(),
                ConstraintSet.create(conditionsGEQ),
                implication.getConclusion(),
                implication.getData());
        res.add(implGEQ);

        if (nextSplit != null) {
            final Set<Constraint> conditionsLEQ =
                this.buildConstraitsLEQ(interpretation, factory, nextSplit, implication.getConditions(), conclusionVariables);
            conditionsLEQ.add(PolyAtom.<BigIntImmutable>create(
                factory.buildFromVariable(nextSplit),
                ConstraintType.GE,
                interpretation,
                null,
                null,
                null,
                -1));

            Set<Constraint> newLEQConclusion;
            if (implication.getConclusion().isConstraintSet()) {
                newLEQConclusion =
                    this.buildConstraitsLEQ(
                        interpretation,
                        factory,
                        nextSplit,
                        (ConstraintSet) implication.getConclusion(),
                        null);
            } else {
                newLEQConclusion =
                    this.buildConstraitsLEQ(
                        interpretation,
                        factory,
                        nextSplit,
                        ConstraintSet.flatCreate(implication.getConclusion()),
                        null);
            }
            final Implication implLEQ =
                Implication.create(
                    implication.getId(),
                    implication.getQuantor(),
                    ConstraintSet.create(conditionsLEQ),
                    ConstraintSet.create(newLEQConclusion),
                    implication.getData());
            res.add(implLEQ);
        }

        return ConstraintSet.create(res);
    }

    protected boolean containsAny(final Set<GPolyVar> sub, final Set<GPolyVar> sup) {
        for (final GPolyVar var : sub) {
            if (sup.contains(var)) {
                return true;
            }
        }
        return false;
    }

    protected Set<Constraint> buildConstraitsLEQ(
        final GInterpretation<BigIntImmutable> interpretation,
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory,
        final GPolyVar splitVar,
        final ConstraintSet orgConditions,
        final Set<GPolyVar> conclusionVariables)
    {
        final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> negSplit =
            factory.concat(
                interpretation.getFactory().getInnerFactory().buildFromCoeff(BigIntImmutable.MINUS_ONE),
                factory.buildVariable(splitVar));
        return this.replacePolyVar(interpretation, factory, splitVar, negSplit, orgConditions, conclusionVariables);
    }

    protected Set<Constraint> replacePolyVar(
        final GInterpretation<BigIntImmutable> interpretation,
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory,
        final GPolyVar polyVar,
        final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> value,
        final ConstraintSet orgConditions,
        final Set<GPolyVar> conclusionVariables)
    {
        final Set<Constraint> conditionsLEQ = new LinkedHashSet<Constraint>();
        final Map<GPolyVar, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> substitution =
            new LinkedHashMap<GPolyVar, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>();
        substitution.put(polyVar, value);
        final VarSubstitutionVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> visitor =
            new VarSubstitutionVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(substitution, factory, null);
        for (final Constraint constraint : orgConditions) {
            if (conclusionVariables == null || conclusionVariables.containsAll(constraint.getPolyVariables())) {
                if (constraint.isPolyAtom()) {
                    final PolyAtom<BigIntImmutable> atom = (PolyAtom<BigIntImmutable>) constraint;
                    conditionsLEQ.add(PolyAtom.<BigIntImmutable>create(
                        visitor.applyTo(atom.getLhs()),
                        atom.getRelation(),
                        interpretation,
                        atom.getTermAtom(),
                        atom.getLeft(),
                        atom.getRight(),
                        atom.getRecommendation()));
                } else {
                    conditionsLEQ.add(constraint);
                }
            }
        }
        return conditionsLEQ;
    }

    protected abstract GPolyVar decideNextSplit(
        Implication implication,
        GInterpretation<BigIntImmutable> interpretation,
        Map<GPolyVar, VarAnalysis> varAnalysis,
        Set<Set<MonomialAnalysis>> useableConstraints,
        Set<GPolyVar> remainingVariable);

}
