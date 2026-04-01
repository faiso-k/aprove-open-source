/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class InfRulePolyRemoveMinMax extends InfRuleSMT {

    @Override
    public InfRuleID getID() {
        return InfRuleID.POLY_REMOVE_MIN_MAX;
    }

    @Override
    public String getLongName() {
        return "Rule Min Max";
    }

    @Override
    public String getName() {
        return "Rule Min Max: removes min / max by case destinction";
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        final Constraint res = this.processImpl(implication, aborter);
        return (res == null ? null : new Pair<Constraint, InfProofStepInfo>(res, null));
    }

    protected Constraint processImpl(final Implication implication, final Abortion aborter) throws AbortionException {
        final IDPGInterpretation interpretation = (IDPGInterpretation) this.getIrc().getPolyInterpretation();
        final MaxMinCollector maxCollector = new MaxMinCollector(interpretation, this.smtEngine, aborter);
        final Set<Constraint> nonPolyCond = new LinkedHashSet<Constraint>();
        List<Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>>> cleanedConditions =
            new ArrayList<Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>>>();
        final Set<Constraint> remainginConditions = new LinkedHashSet<Constraint>(implication.getConditions());
        {
            final Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>> initCondition =
                new Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>>(
                    new LinkedHashSet<PolyAtom<BigIntImmutable>>(0),
                    new LinkedHashSet<PolyAtom<BigIntImmutable>>(0));
            final Iterator<Constraint> remainingIter = remainginConditions.iterator();
            while (remainingIter.hasNext()) {
                final Constraint condition = remainingIter.next();
                if (condition.isPolyAtom()) {
                    final PolyAtom<BigIntImmutable> atom = (PolyAtom<BigIntImmutable>) condition;
                    if (!atom.getLhs().hasMaxMin()) {
                        if (atom.isLinear()) {
                            initCondition.x.add(atom);
                        } else {
                            initCondition.y.add(atom);
                        }
                        remainingIter.remove();
                    }
                }
            }
            cleanedConditions.add(initCondition);
        }
        for (final Constraint condition : remainginConditions) {
            if (condition.isPolyAtom()) {
                if (aborter != null) {
                    aborter.checkAbortion();
                }
                final PolyAtom<BigIntImmutable> atom = (PolyAtom<BigIntImmutable>) condition;
                if (atom.getTag(this.getID()) != null) {
                    final boolean linear = atom.isLinear();
                    for (final Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>> condPair : cleanedConditions)
                    {
                        if (linear) {
                            condPair.x.add(atom);
                        } else {
                            condPair.y.add(atom);
                        }
                    }
                    continue;
                }
                atom.setTag(this.getID(), Boolean.TRUE);

                final List<Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>>> oldConditions =
                    cleanedConditions;
                cleanedConditions =
                    new ArrayList<Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>>>();
                for (final Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>> condPair : oldConditions)
                {
                    maxCollector.clearStack();
                    maxCollector.applyTo(atom.getLhs(), condPair.x, condPair.y);
                    final ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> values =
                        maxCollector.getValues();
                    for (final Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> value : values)
                    {
                        PolyAtom<BigIntImmutable> newValue;
                        if (value.z == atom.getLhs()) {
                            newValue = atom;
                        } else {
                            newValue =
                                PolyAtom.create(
                                    value.z,
                                    atom.getRelation(),
                                    interpretation,
                                    atom.getTermAtom(),
                                    atom.getLeft(),
                                    atom.getRight(),
                                    atom.getRecommendation());
                        }
                        if (newValue.isLinear()) {
                            value.x.add(newValue);
                        } else {
                            value.y.add(newValue);
                        }
                        if (this.isSolvable(value.x, interpretation, aborter)) {
                            cleanedConditions
                                .add(new Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>>(
                                    value.x,
                                    value.y));
                        }
                    }
                }
            } else {
                nonPolyCond.add(condition);
            }
        }

        final List<Implication> newImpls = new ArrayList<Implication>();
        final ConstraintSet conclusions = ConstraintSet.flatCreate(implication.getConclusion());

        for (final Pair<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>> condPair : cleanedConditions) {
            List<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>>> acc =
                new ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>>>();
            acc.add(new Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>>(
                condPair.x,
                condPair.y,
                new LinkedHashSet<Constraint>(0)));
            for (final Constraint conclusion : conclusions) {
                if (conclusion.isPolyAtom()) {
                    if (aborter != null) {
                        aborter.checkAbortion();
                    }
                    final PolyAtom<BigIntImmutable> atom = (PolyAtom<BigIntImmutable>) conclusion;
                    final List<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>>> oldAcc =
                        acc;
                    acc =
                        new ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>>>();
                    for (final Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>> ac : oldAcc)
                    {
                        maxCollector.clearStack();
                        maxCollector.applyTo(atom.getLhs(), ac.x, ac.y);
                        final ArrayList<Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>> values =
                            maxCollector.getValues();
                        for (final Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> value : values)
                        {
                            final Set<Constraint> c = new LinkedHashSet<Constraint>(ac.z);
                            if (value.z == atom.getLhs()) {
                                c.add(atom);
                            } else {
                                c.add(PolyAtom.create(
                                    value.z,
                                    atom.getRelation(),
                                    interpretation,
                                    atom.getTermAtom(),
                                    atom.getLeft(),
                                    atom.getRight(),
                                    atom.getRecommendation()));
                            }
                            acc
                                .add(new Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>>(
                                    value.x,
                                    value.y,
                                    c));
                        }
                    }
                } else {
                    for (final Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>> ac : acc)
                    {
                        ac.z.add(conclusion);
                    }
                }
            }
            for (final Triple<Set<PolyAtom<BigIntImmutable>>, Set<PolyAtom<BigIntImmutable>>, Set<Constraint>> ac : acc)
            {
                final Set<Constraint> newConds = new LinkedHashSet<Constraint>(nonPolyCond);
                newConds.addAll(ac.x);
                newConds.addAll(ac.y);
                final Implication impl =
                    Implication.create(
                        implication.getQuantor(),
                        ConstraintSet.create(newConds),
                        ConstraintSet.create(ac.z),
                        implication.getData());
                impl.setTag(this.getID(), Boolean.TRUE);
                newImpls.add(impl);
            }
        }
        return ConstraintSet.create(newImpls);
    }
}
