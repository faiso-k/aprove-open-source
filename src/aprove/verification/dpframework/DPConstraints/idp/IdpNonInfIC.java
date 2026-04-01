/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.Predicate.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class IdpNonInfIC extends IdpInductionCalculus {

    protected final IDPNonInfInterpretation idpInterpretation;

    private final int stategyMode;

    public final StrategyLevel replaceContextPredefSymbolsStrategy = new StrategyLevel(
        "replaceContextPredefSymbolsStrategy",
        new InfRule[] {
        // new InfRuleIdpReplacePredefSymbols()
        },
        true);

    public static final int TERM_STRATEGY = 0;
    public static final int POLY_STRATEGY = 1;
    public static final int FULL_STRATEGY = 2;
    public static final int VALIDATE_FULL_STRATEGY = 3;

    protected final FunctionSymbol fixedIntConstant;
    final IDPNonInfInterpretation polyInterpretation;

    public IdpNonInfIC(
        IDPProblem idp,
        InductionCalculusProof proof,
        IDPOptions options,
        IDPNonInfInterpretation polyInterpretation,
        int stategyMode,
        Abortion aborter)
    {
        super(idp, proof, options, polyInterpretation, null, aborter);
        this.polyInterpretation = polyInterpretation;
        FreshNameGenerator freshName =
            new FreshNameGenerator(idp.getRuleAnalysis().getFunctionSymbols(), FreshNameGenerator.FRIENDLYNAMES);
        this.fixedIntConstant = FunctionSymbol.create(freshName.getFreshName("fixInt", false), 1);
        this.idpInterpretation = polyInterpretation;
        this.stategyMode = stategyMode;
    }

    @Override
    protected void init() {
        super.init();
        this.constructorSymbols.add(this.fixedIntConstant);
    }

    @Override
    protected Constraint createConclusion(VariableRenamedPath variableRenamedPath, int position) {
        if (this.polyInterpretation.isTupleNat()) {
            return super.createConclusion(variableRenamedPath, position);
        }
        ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>> step = variableRenamedPath.getPath().get(position);
        TRSSubstitution sigma = TRSSubstitution.create(step.y, true);
        TRSFunctionApplication leftSigma = step.x.rule.getLeft().applySubstitution(sigma);
        TRSTerm rightSigma = step.x.rule.getRight().applySubstitution(sigma);

        Set<Constraint> res = new LinkedHashSet<Constraint>();
        res.add(super.createConclusion(variableRenamedPath, position));
        if (aprove.Globals.useAssertions) {
            assert (this.idpInterpretation.getNonInfBound() != null) : "need non inf constant";
        }
        res.add(Predicate.create(
            leftSigma,
            PredefinedUtil.createInt(BigInteger.ZERO),
            Kind.NonInfConstantCompare,
            GeneralizedRule.create(
                leftSigma,
                rightSigma,
                step.x.rule.getLhsInStandardRepresentation(),
                step.x.rule.getRhsInStandardRepresentation()),
            RelDependency.Wild,
            RelDependency.Wild));
        return ConstraintSet.create(res);
    }

    @Override
    protected StrategyLevel[] initLeveledStrategy() {
        switch (this.stategyMode) {
        case TERM_STRATEGY:
            return new StrategyLevel[] {this.startStrategy, null, this.standardStrategy, this.preFinalStrategy, null };
        case POLY_STRATEGY:
            return new StrategyLevel[] {this.finalStrategy, null };
        case FULL_STRATEGY:
            return new StrategyLevel[] {
                this.startStrategy,
                null,
                this.standardStrategy,
                this.preFinalStrategy,
                null,
                this.finalStrategy,
                null };
        case VALIDATE_FULL_STRATEGY:
            return new StrategyLevel[] {
                this.startStrategy,
                null,
                this.standardStrategy,
                this.preFinalStrategy,
                null,
                this.replaceContextPredefSymbolsStrategy,
                this.finalStrategy,
                this.finalCleanupStrategy,
                null };
        default:
            return new StrategyLevel[0];
        }
    }

    public FunctionSymbol getFixedIntConstant() {
        return this.fixedIntConstant;
    }

    /*
    protected void addUsableRulesConstraints(Collection<Implication> constraints) {
        IdpQUsableRules usableRules = idp.getRuleAnalysis().getUseableRules(null);
        Set<OrderPolyConstraint<BigIntImmutable>> activeConstraints =
            new HashSet<OrderPolyConstraint<BigIntImmutable>>();

        Map<QActiveCondition, GPolyVar> activeConditions =
            new LinkedHashMap<QActiveCondition, GPolyVar>();
        OPCRange<BigIntImmutable> boolRange = new OPCRange<BigIntImmutable>(polyInterpretation.getRing().zero(), polyInterpretation.getRing().one());
        IDPGInterpretation polyInterpretation = ((IDPGInterpretation)this.polyInterpretation);

        Map<GeneralizedRule, IActiveCondition> usableActive = new HashMap<GeneralizedRule, IActiveCondition>(usableRules.getActive());
        for (Map.Entry<GeneralizedRule, IActiveCondition> usableRule : usableActive.entrySet()) {
            try {
                Term left = usableRule.getKey().getLhsInStandardRepresentation();
                Term right = usableRule.getKey().getRhsInStandardRepresentation();

                // build rule constraint
                GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> constraint =
                    polyInterpretation.getFactory().minus(polyInterpretation.interpretTerm(left), polyInterpretation.interpretTerm(right));

                if (usableRule.getValue() != IActiveCondition.TRUE) {
                    // Return a variable that, when set to 1, denotes the rule is
                    // usable. The function getActiveCondition also creates the
                    // constraints that are needed to decide how to set the value
                    // of that variable.
                    GPoly<BigIntImmutable, GPolyVar> acCoeff = polyInterpretation.getActiveCondition(usableRule.getValue(), activeConstraints, activeConditions, boolRange, null);
                    // multiply it with active condition
                    GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> acPoly =
                        polyInterpretation.getFactory().getFactory().buildFromCoeff(acCoeff);
                    constraint =
                        polyInterpretation.getFactory().getFactory().times(constraint, acPoly);
                }
                System.out.println("Usable2 : " + left + " >= " + right);
                System.out.println("[" + left + "] = " + polyString(polyInterpretation, polyInterpretation.interpretTerm(left)) + "\n[" + right + "] = " + polyString(polyInterpretation, polyInterpretation.interpretTerm(right)) + "\n -> " + polyString(polyInterpretation, constraint));
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
    }
    */

}
