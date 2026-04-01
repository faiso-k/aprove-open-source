/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class StrategyLevelToPoly extends StrategyLevel {

    protected IdpInductionCalculus irc;

    private final InfRulePolyRemoveMinMax maxRemovalRule;
    private final InfRuleToPoly polyRule;
    private final InfRulePolySimplify polySimplify;

    public StrategyLevelToPoly(
        final String name,
        final IdpInductionCalculus irc,
        final InfRule[] strategy,
        final boolean repeat)
    {
        super(name, strategy, repeat);
        this.irc = irc;
        this.polyRule = new InfRuleToPoly();
        this.polyRule.initContext(irc);
        this.maxRemovalRule = new InfRulePolyRemoveMinMax();
        this.maxRemovalRule.initContext(irc);
        this.polySimplify = new InfRulePolySimplify();
        this.polySimplify.initContext(irc);
    }

    @Override
    public
        void
        prepare(final List<Implication> constraints, final InductionCalculusProof proof, final Abortion aborter)
            throws AbortionException
    {
        //System.out.println("TO POLY #######################");
        // irc.show(constraints);
        // System.out.println("BigIntImmutable: " + constraints.size());
        this.applyRule(this.polyRule, constraints, proof, aborter);
        // System.out.println("====================================================");
        // irc.show(constraints);

        this.applyRule(this.polySimplify, constraints, proof, aborter);
        this.applyRule(this.maxRemovalRule, constraints, proof, aborter);
        // System.out.println(">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>");
        // irc.show(constraints);
    }

    protected void applyRule(
        final InfRule infRule,
        final List<Implication> constraints,
        final InductionCalculusProof proof,
        final Abortion aborter) throws AbortionException
    {
        int readyCounter = 0;
        int toSize = constraints.size();
        ////Map<FunctionSymbol, Integer> usableRules = new LinkedHashMap<FunctionSymbol, Integer>();
        // System.out.println("ToSize: " + toSize);
        ////int tmp = 0;
        while (readyCounter < toSize) {
            // apply to poly rule
            final Implication current = constraints.get(readyCounter);
            // System.out.println("ApplyTo: " + readyCounter + " " + toSize  + " of " + (++tmp));

            final Pair<Constraint, InfProofStepInfo> res = infRule.applyToImplication(current, aborter);
            if (res != null && res.x != current) {
                // System.out.println("Res: " + current + "\n >=>=> " + res);
                proof.appliedRule(
                    current,
                    infRule,
                    new LinkedList<Implication>(constraints),
                    this.irc.getMark(),
                    res.y,
                    readyCounter);
                //System.out.println("==========================================================================================>"+this.lastRule.getClass().getSimpleName());
                if (res.x.isConstraintSet()) {
                    constraints.remove(readyCounter);
                    // TODO fixed position only used for debugging
                    if (aprove.Globals.useAssertions) {
                        for (final Constraint c : (ConstraintSet) (res.x)) {
                            this.assertPolyUsableAtoms(c);
                        }
                    }
                    constraints.addAll((Set) res.x);
                    toSize--;
                } else {
                    this.assertPolyUsableAtoms(res.x);
                    constraints.set(readyCounter, (Implication) (res.x));
                    readyCounter++;
                }
            } else {
                readyCounter++;
            }
            aborter.checkAbortion();
        }
        // irc.show(constraints);
    }

    /*
    protected void addStrictConstraints(Collection<Implication> constraints) {
        // TODO: use strictMode
        IDPProblem idp = irc.getIdp();
        GInterpretation<BigIntImmutable> interpretation = irc.getPolyInterpretation();
        OrderPolyFactory<BigIntImmutable> factory = interpretation.getFactory();

        Set<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> polys = new HashSet<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>();
        for (GeneralizedRule rule : idp.getP()) {
            polys.add(factory.getFactory().minus(interpretation.interpretTerm(rule.getLeft()).unwrap(), interpretation.interpretTerm(rule.getRight()).unwrap()));
        }
        constraints.add(Implication.create(IdpInductionCalculus.emptyQuantor, IdpInductionCalculus.emptyConditions, PolyAtom.create(factory.getFactory().plus(polys), ConstraintType.GT, null)));
    }

    protected void addConstantConstraints(Collection<Implication> constraints) {
        IDPProblem idp = irc.getIdp();
        GInterpretation<BigIntImmutable> interpretation = irc.getPolyInterpretation();
        GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> factory = interpretation.getFactory().getFactory();

        // TODO: Degree
        interpretation.extend(IdpInductionCalculus.FRESH_CONST, 1);
        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> constPoly = interpretation.interpretTerm(FunctionApplication.createFunctionApplication(IdpInductionCalculus.FRESH_CONST, ImmutableCreator.create(new ArrayList<Term>(0))));

        Set<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> polys = new HashSet<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>();
        for (GeneralizedRule rule : idp.getP()) {
            polys.add(factory.minus(interpretation.interpretTerm(rule.getLeft()).unwrap(), constPoly));
        }
        constraints.add(Implication.create(IdpInductionCalculus.emptyQuantor, IdpInductionCalculus.emptyConditions, PolyAtom.create(factory.plus(polys), ConstraintType.GE, null)));
    }

    protected void addUsableRulesConstraints(Map<FunctionSymbol, Integer> usableRules2, Collection<Implication> constraints) {
        IDPProblem idp = irc.getIdp();
        IdpQUsableRules usableRules = idp.getRuleAnalysis().getUseableRules(null);
        GInterpretation<BigIntImmutable> interpretation = irc.getPolyInterpretation();
        Set<OrderPolyConstraint<BigIntImmutable>> activeConstraints =
            new HashSet<OrderPolyConstraint<BigIntImmutable>>();

        Map<QActiveCondition, GPolyVar> activeConditions =
            new LinkedHashMap<QActiveCondition, GPolyVar>();
        OPCRange<BigIntImmutable> boolRange = new OPCRange<BigIntImmutable>(interpretation.getRing().zero(), interpretation.getRing().one());

        Map<GeneralizedRule, QActiveCondition> usableActive = new HashMap<GeneralizedRule, QActiveCondition>(usableRules.getActive());
        Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap = idp.getRuleAnalysis().getRAnalysis().getRuleMap();
        for (Map.Entry<FunctionSymbol, Integer> u : usableRules2.entrySet()) {
            ImmutableSet<GeneralizedRule> rls = ruleMap.get(u.getKey());
            if (rls != null) {
                if (u.getValue() > 0) {
                    for (GeneralizedRule r : rls) {
                        usableActive.put(r, QActiveCondition.TRUE);
                    }
                }
                // add inverse rules
                if (u.getValue() == -1 || u.getValue() == 2) {
                    for (GeneralizedRule r : rls) {
                        constraints.add(getRuleConstraint(interpretation, r));
                    }
                }
            }
        }

        for (Map.Entry<GeneralizedRule, QActiveCondition> usableRule : usableActive.entrySet()) {
            try {
                Term left = usableRule.getKey().getLhsInStandardRepresentation();
                Term right = usableRule.getKey().getRhsInStandardRepresentation();

                // build rule constraint
                GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> constraint =
                    interpretation.getFactory().minus(interpretation.interpretTerm(left), interpretation.interpretTerm(right));

                if (usableRule.getValue() != QActiveCondition.TRUE) {
                    // Return a variable that, when set to 1, denotes the rule is
                    // usable. The function getActiveCondition also creates the
                    // constraints that are needed to decide how to set the value
                    // of that variable.
                    GPoly<BigIntImmutable, GPolyVar> acCoeff = interpretation.getActiveCondition(usableRule.getValue(), activeConstraints, activeConditions, boolRange, null);
                    // multiply it with active condition
                    GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> acPoly =
                        interpretation.getFactory().getFactory().buildFromCoeff(acCoeff);
                    constraint =
                        interpretation.getFactory().getFactory().times(constraint, acPoly);
                }
                System.out.println("Usable2 : " + left + " >= " + right);
                System.out.println("[" + left + "] = " + polyString(interpretation, interpretation.interpretTerm(left)) + "\n[" + right + "] = " + polyString(interpretation, interpretation.interpretTerm(right)) + "\n -> " + polyString(interpretation, constraint));
                constraints.add(Implication.create(IdpInductionCalculus.emptyQuantor, IdpInductionCalculus.emptyConditions, PolyAtom.create(constraint, ConstraintType.GE, null)));
            } catch (AbortionException e) {
                // should never occur since no aborter used
                e.printStackTrace();
            }
        }
    }

    protected Implication getRuleConstraint(GInterpretation<BigIntImmutable> interpretation, GeneralizedRule r) {
        Term left = r.getLhsInStandardRepresentation();
        Term right = r.getRhsInStandardRepresentation();
        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> constraint =
            interpretation.getFactory().minus(interpretation.interpretTerm(right), interpretation.interpretTerm(left));
        return Implication.create(IdpInductionCalculus.emptyQuantor, IdpInductionCalculus.emptyConditions, PolyAtom.create(constraint, ConstraintType.GE, null));
    }

    private String polyString(GInterpretation<BigIntImmutable> interpretation, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> constraint) {
        return interpretation.getFactory().wrap(constraint).exportFlatDeep(interpretation.getFvInner(), interpretation.getFvOuter(), new PLAIN_Util());
    }*/

    protected void assertPolyUsableAtoms(final Constraint constraint) {
        if (constraint.isImplication()) {
            final Implication i = (Implication) constraint;
            this.assertPolyUsableAtoms(i.getConditions());
            this.assertPolyUsableAtoms(i.getConclusion());
        } else if (constraint.isConstraintSet()) {
            for (final Constraint c : (ConstraintSet) constraint) {
                this.assertPolyUsableAtoms(c);
            }
        } else {
            if (aprove.Globals.useAssertions) {
                assert (constraint.isPolyAtom() || constraint.isUsableAtom()) : "no poly/usable atom: " + constraint;
            }
        }
    }

}
