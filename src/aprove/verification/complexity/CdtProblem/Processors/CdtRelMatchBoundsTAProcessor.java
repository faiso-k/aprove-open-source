package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBounds.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class CdtRelMatchBoundsTAProcessor extends CdtProblemProcessor {

    TRSBounds.STAStrategy sTAS;
    TRSBounds.ConflictResolvingStrategy cRS;
    TRSBounds.WhenToBuildTAStrategy wTBTA;
    TRSBounds.QuasiDetStrategy qDS;

    final int mCTR; // MAX_CONFLICTS_TO_RESOLVE
    final int mTOA; // MAX_TRANSITIONS_OF_A
    final int mSOA; // MAX_STATES_OF_A

    @ParamsViaArgumentObject
    public CdtRelMatchBoundsTAProcessor(Arguments arguments) {
        this.sTAS = arguments.sTAS;
        this.cRS = arguments.cRS;
        this.wTBTA = arguments.wTBTA;
        this.qDS = arguments.qDS;
        this.mCTR = arguments.MAX_CONFLICTS_TO_RESOLVE;
        this.mTOA = arguments.MAX_TRANSITIONS_OF_A;
        this.mSOA = arguments.MAX_STATES_OF_A;
    }

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return this.isNonDuplicating(obl.getR()) && this.isNonDuplicatingCdt(obl.getTuples());
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter) throws AbortionException {

        boolean leftLinear = CollectionUtils.isLeftLinear(cdtProblem.getR()) && this.isLeftLinearCdt(cdtProblem.getTuples());
        aborter.checkAbortion();

        Cdt ruleToRemove = cdtProblem.getS().iterator().next();

        TRSBounds b = null;
        TRSBounds.Certificate certificate = null;
        if (leftLinear) {
            b = new TRSBounds(cdtProblem, ruleToRemove, TRSBounds.Bound.MATCHRT, this.sTAS, this.cRS, this.wTBTA, this.qDS, this.mCTR, this.mTOA,
                            this.mSOA);
        } else {
            b = new TRSBounds(cdtProblem, ruleToRemove, TRSBounds.Bound.MATCHRAISERT, this.sTAS, this.cRS, this.wTBTA, this.qDS, this.mCTR,
                            this.mTOA, this.mSOA);
        }

        certificate = b.getCertificate(aborter);

        if (certificate != null) {
            LinkedHashSet<Cdt> newS = new LinkedHashSet<Cdt>(cdtProblem.getS());
            newS.remove(ruleToRemove);
            LinkedHashSet<Cdt> newK = new LinkedHashSet<Cdt>(cdtProblem.getK());
            newK.add(ruleToRemove);
            CdtProblem newCdtProblem = cdtProblem.createSubproblem(cdtProblem.getGraph(), ImmutableCreator.create(newS),
                ImmutableCreator.create(newK));
            ComplexityValue upperBound = (ComplexityValue.linear());
            return ResultFactory.proved(newCdtProblem, UpperBound.create(new SumComputation(upperBound)), new CdtRelMatchBoundsTAProof(ruleToRemove,
                            certificate));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private boolean isNonDuplicating(Set<Rule> R) {
        boolean isNonDuplicating = true;
        for (Rule r : R) {

            if (r.isDuplicating()) {
                isNonDuplicating = false;
            }
        }
        return isNonDuplicating;
    }

    private boolean isLeftLinearCdt(Set<Cdt> cdtSet) {
        boolean isLeftLinear = true;
        for (Cdt cdt : cdtSet) {
            Rule r = cdt.getRule();
            TRSFunctionApplication lhs = r.getLeft();
            if (!lhs.isLinear()) {
                isLeftLinear = false;
            }
        }
        return isLeftLinear;
    }

    private boolean isNonDuplicatingCdt(Set<Cdt> cdtSet) {
        boolean isNonDuplicating = true;
        for (Cdt cdt : cdtSet) {
            Rule r = cdt.getRule();
            if (r.isDuplicating()) {
                isNonDuplicating = false;
            }
        }
        return isNonDuplicating;
    }

    private class CdtRelMatchBoundsTAProof extends CpxProof {

        private final TRSBounds.Certificate certificate;
        private final Set<Cdt> rulesToRemove;

        public CdtRelMatchBoundsTAProof(Cdt ruleToRemove, Certificate certificate) {
            this.rulesToRemove = new LinkedHashSet<Cdt>();
            this.rulesToRemove.add(ruleToRemove);
            this.certificate = certificate;
        }

        /**
         * Returns the output string.
         */
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            /*String typeOfBound = "";
            if (this.certificate.getBound() == TRSBounds.Bound.TOPDP) {
                typeOfBound = "Top-";
            } else if (this.certificate.getBound() == TRSBounds.Bound.MATCHDP) {
                typeOfBound = "Match-";
            }
            if (this.certificate.getBound() == TRSBounds.Bound.TOPRAISEDP || this.certificate.getBound() == TRSBounds.Bound.MATCHRAISEDP) {
                typeOfBound += "(raise-)";
            }

            typeOfBound += "DP-";

            result.append("The DP-Problem (P, R) could be shown to be " + typeOfBound + "Bounded "
                            + o.cite(new Citation[] {Citation.TAB_NONLEFTLINEAR }) + " by " + this.certificate.getBoundedBy() + " for the Rule: "
                            + o.set(this.rulesToRemove, Export_Util.RULES) + "by considering the usable rules: ");
            this.result.append(o.linebreak());
            result.append("The tree automaton used to show the " + typeOfBound + "Boundedness consists of "
                    + this.certificate.getTreeAutomaton().getTransitions()
                            .size()
                    + " transitions and of which there are "
                    + this.certificate.getTreeAutomaton().getEpsTransitions()
                            .size()
                    + " epsilon transitions and "
                    +
                + this.certificate.getTreeAutomaton().getAllStates().size() + " states.");
            //this.result.append("The compatible tree automaton used to show the " + typeOfBound + "Boundedness is represented by: ");
            this.result.append(o.linebreak());*/
            this.certificate.printTA(o, result);

            return result.toString();
        }
    }

    public static class Arguments {
        public TRSBounds.STAStrategy sTAS = TRSBounds.STAStrategy.RC_SPLIT;
        public TRSBounds.ConflictResolvingStrategy cRS = TRSBounds.ConflictResolvingStrategy.KMS;
        public TRSBounds.WhenToBuildTAStrategy wTBTA = TRSBounds.WhenToBuildTAStrategy.BUILD_TA_AFTER_RESOLVING_ONE_CONFLICT;
        public TRSBounds.QuasiDetStrategy qDS = TRSBounds.QuasiDetStrategy.APPROX;
        public int MAX_CONFLICTS_TO_RESOLVE = 10000;
        public int MAX_TRANSITIONS_OF_A = 10000;
        public int MAX_STATES_OF_A = 4000;
    }

}
