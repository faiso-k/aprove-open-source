package aprove.verification.oldframework.IntTRS.CaseAnalysis;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Finds inductive conditions and - in case of success - returns systems to be
 * solved instead.
 * @author Matthias Hoelzel
 */
public class CaseAnalysisProcessor extends Processor.ProcessorSkeleton {
    private final Arguments args;

    /** Some arguments */
    public static class Arguments {
        /** Order your order here!*/
        CaseAnalysisMode mode = CaseAnalysisMode.DEFAULT;
    }

    public CaseAnalysisProcessor(final Arguments arguments) {
        this.args = arguments;
    }

    public CaseAnalysisProcessor() {
        this.args = new Arguments();
    }

    public void setMode(final CaseAnalysisMode val) {
        this.args.mode = val;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem inputProblem;
        if (obl instanceof IRSProblem) {
            inputProblem = ((IRSProblem) obl).linearizeLeftSides();
        } else {
            inputProblem = (new IRSProblem((IRSwTProblem) obl)).linearizeLeftSides();
        }
        final CaseAnalysisProof proof = new CaseAnalysisProof();
        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);

        final RulePreparation rp = new RulePreparation(ng);
        final IRSProblem intTRSProblem = rp.preprareIntTRSProblem(inputProblem);

        final InductiveConditionFinder icf =
            new InductiveConditionFinder(intTRSProblem, new FullSharingFactory<SMTLIBTheoryAtom>(), this.args, aborter,
                ng);

        final GEZeroCondition inductiveCond = icf.getInductiveCondition();
        if (inductiveCond == null) {
            return ResultFactory.unsuccessful();
        } else {
            proof.setInductiveCondition(inductiveCond);
            final LinkedHashSet<IGeneralizedRule> satRules = new LinkedHashSet<>();
            final LinkedHashSet<IGeneralizedRule> unsatRules = new LinkedHashSet<>();

            for (final IGeneralizedRule rule : intTRSProblem.getRules()) {
                final VarPolynomial toBeGEZero = inductiveCond.buildCorrespondingPolynomial(rule.getLeft(), ng);

                if (toBeGEZero == null) {
                    satRules.add(rule);
                    unsatRules.add(rule);
                    continue;
                }

                final TRSTerm toBeGEZeroTerm = toBeGEZero.toTerm();

                TRSTerm conditionTerm = rule.getCondTerm();
                if (conditionTerm == null) {
                    conditionTerm = ToolBox.buildTrue();
                }

                satRules
                    .add(IGeneralizedRule.create(
                        rule.getLeft(),
                        rule.getRight(),
                        ToolBox.buildAnd(
                            conditionTerm,
                            ToolBox.buildGe(toBeGEZeroTerm, ToolBox.buildInt(BigInteger.ZERO)))));

                unsatRules
                    .add(IGeneralizedRule.create(
                        rule.getLeft(),
                        rule.getRight(),
                        ToolBox.buildAnd(
                            conditionTerm,
                            ToolBox.buildLt(toBeGEZeroTerm, ToolBox.buildInt(BigInteger.ZERO)))));
            }

            final LinkedList<IRSProblem> toSolve = new LinkedList<>();

            toSolve.add(new IRSProblem(ImmutableCreator.create(satRules)));
            toSolve.add(new IRSProblem(ImmutableCreator.create(unsatRules)));

            return ResultFactory.provedAnd(toSolve, YNMImplication.EQUIVALENT, proof);
        }
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me), Matthias Hoelzel (blame cotto instead)
     */
    class CaseAnalysisProof extends DefaultProof {
        private GEZeroCondition condition;

        /** Creates the proof. */
        public CaseAnalysisProof() {
            super();
            this.shortName = "CaseAnalysis";
            this.longName = "CaseAnalysisProcessor";
        }

        public void setInductiveCondition(final GEZeroCondition inductiveCond) {
            this.condition = inductiveCond;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            if (this.condition == null) {
                sb.append(eu.escape("Applied a case analysis."));
            } else {
                sb.append(eu.escape("Found the following inductive condition: "));
                sb.append(eu.linebreak());
                for (final Pair<TRSFunctionApplication, VarPolynomial> p : this.condition.getGeZeroTerms().values()) {
                    sb.append(p.getKey().export(eu));
                    sb.append(eu.escape(": "));
                    sb.append(p.getValue().export(eu));
                    sb.append(eu.geSign());
                    sb.append(VarPolynomial.ZERO.export(eu));
                    // ;)
                    sb.append(eu.linebreak());
                }
            }
            return sb.toString();
        }
    }
}
