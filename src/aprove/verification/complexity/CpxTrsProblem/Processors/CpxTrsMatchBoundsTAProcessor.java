package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * @author Marcel Klinzing
 */
public class CpxTrsMatchBoundsTAProcessor extends RuntimeComplexityTrsProcessor {

    private final static ComplexityYNM linear = ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.linear());
    TRSBounds.STAStrategy sTAS;
    TRSBounds.ConflictResolvingStrategy cRS;
    TRSBounds.WhenToBuildTAStrategy wTBTA;
    TRSBounds.QuasiDetStrategy qDS;

    final int mCTR; // MAX_CONFLICTS_TO_RESOLVE
    final int mTOA; // MAX_TRANSITIONS_OF_A
    final int mSOA; // MAX_STATES_OF_A


    @ParamsViaArgumentObject
    public CpxTrsMatchBoundsTAProcessor(final Arguments arguments) {
        this.sTAS = arguments.sTAS;
        this.cRS = arguments.cRS;
        this.wTBTA = arguments.wTBTA;
        this.qDS = arguments.qDS;
        this.mCTR = arguments.MAX_CONFLICTS_TO_RESOLVE;
        this.mTOA = arguments.MAX_TRANSITIONS_OF_A;
        this.mSOA = arguments.MAX_STATES_OF_A;
    }

    @Override
    public boolean isRuntimeComplexityTrsApplicable(final RuntimeComplexityTrsProblem obl) {
        final Set<Rule> R = obl.getR();
        if (Options.certifier.isCeta() && !this.isLeftLinear(R)) {
            // CeTA demands state-compatible, deterministic automata as output,
            // but this implementation only generates quasi-deterministic automata.
            // There is an automatic conversion from the latter to the former,
            // but this remains to be implemented.
            return false;
        }
        return this.isNonDuplicating(R);
    }

    @Override
    public Result processRuntimeComplexityTrs(final RuntimeComplexityTrsProblem cpxTrs, final Abortion aborter) throws AbortionException {
        final Set<Rule> R = cpxTrs.getR();

        if (Globals.useAssertions) {
            assert (this.isNonDuplicating(R));
        }

        final boolean leftLinear = this.isLeftLinear(R);
        aborter.checkAbortion();

        TRSBounds b = null;
        TRSBounds.Certificate certificate = null;
        if (leftLinear) {
            b = new TRSBounds(cpxTrs, TRSBounds.Bound.MATCH, this.sTAS, this.cRS, this.wTBTA, this.qDS, this.mCTR, this.mTOA, this.mSOA);
        } else {
            final boolean deactivate = true;
            // deactivated matchbounds for non-left-linear TRSs, since
            // implementation is buggy: for tpdb/Runtime_Complexity_Innermost_Rewriting/Transformed_CSR_04/Ex16_Luc06_C.xml
            // the deterministic part of the generated quasi-det. automaton is not really deterministic !!
            // once this is fixed, one can activate the code again
            if (deactivate) {
                return ResultFactory.unsuccessful();
            }
            b = new TRSBounds(cpxTrs, TRSBounds.Bound.MATCHRAISE, this.sTAS, this.cRS, this.wTBTA, this.qDS, this.mCTR, this.mTOA, this.mSOA);
        }

        certificate = b.getCertificate(aborter);

        if (certificate != null) {
            return ResultFactory.provedWithValue(CpxTrsMatchBoundsTAProcessor.linear, new CpxTrsMatchBoundsTAProof(certificate, cpxTrs));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    public static class Arguments {
        public TRSBounds.STAStrategy sTAS = TRSBounds.STAStrategy.RC_SPLIT;
        public TRSBounds.ConflictResolvingStrategy cRS = TRSBounds.ConflictResolvingStrategy.NSFEPS;
        public TRSBounds.WhenToBuildTAStrategy wTBTA = TRSBounds.WhenToBuildTAStrategy.BUILD_TA_AFTER_RESOLVING_ONE_CONFLICT;
        public TRSBounds.QuasiDetStrategy qDS = TRSBounds.QuasiDetStrategy.APPROX;
        public int MAX_CONFLICTS_TO_RESOLVE = 5000;
        public int MAX_TRANSITIONS_OF_A = 3000;
        public int MAX_STATES_OF_A = 1800;
    }

    private boolean isLeftLinear(final Set<Rule> R) {
        boolean isLeftLinear = true;
        for (final Rule r : R) {
            if (!(r.getLeft().isLinear())) {
                isLeftLinear = false;
            }
        }
        return isLeftLinear;
    }

    private boolean isNonDuplicating(final Set<Rule> R) {
        boolean isNonDuplicating = true;
        for (final Rule r : R) {

            if (r.isDuplicating()) {
                isNonDuplicating = false;
            }
        }
        return isNonDuplicating;
    }

    private class CpxTrsMatchBoundsTAProof extends CpxProof {

        private final TRSBounds.Certificate certificate;
        private final BasicObligation origObl;

        public CpxTrsMatchBoundsTAProof(
            final TRSBounds.Certificate certificate,
 final BasicObligation origObl)
        {
            this.certificate = certificate;
            this.origObl = origObl;
        }

        /**
         * Returns the output string.
         * @author Marcel Klinzing
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            String typeOfBound;
            if (this.certificate.getBound() == TRSBounds.Bound.MATCH) {
                typeOfBound = "Match-";
            } else /* certificate.getBound() == TRSBounds.Bound.MATCH */{
                typeOfBound = "Match(-raise)-";
            }

            result.append("A linear upper bound on the runtime complexity of the TRS R could be shown with a " + typeOfBound + "Bound"
                            + o.cite(new Citation[] {Citation.TAB_LEFTLINEAR, Citation.TAB_NONLEFTLINEAR })
                            + " (for contructor-based start-terms) of " + this.certificate.getBoundedBy() + ". ");

            /*result.append(o.linebreak());
            result.append(o.linebreak());
            result.append("The compatible tree automaton used to show the " + typeOfBound
                            + "Boundedness (for constructor-based start-terms) consists of "
                + this.certificate.getTreeAutomaton().getTransitions().size() + " transitions and of which there are "
                + this.certificate.getTreeAutomaton().getEpsTransitions().size() + " epsilon transitions and "
                            + this.certificate.getTreeAutomaton().getAllStates().size() + " states.");*/

            result.append(o.linebreak());
            result.append(o.linebreak());
            result.append("The compatible tree automaton used to show the " + typeOfBound
                            + "Boundedness (for constructor-based start-terms) is represented by: ");
            result.append(o.linebreak());
            this.certificate.printTA(o, result);

            return result.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            return this.positiveTag().create(doc, this.certificate.toCPF(doc, xmlMetaData));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }
}
