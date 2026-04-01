package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * @author Marcel Klinzing
 */
public class QTRSRoofMatchBoundsTAProcessor extends QTRSProcessor {

    TRSBounds.STAStrategy sTAS;
    TRSBounds.ConflictResolvingStrategy cRS;
    TRSBounds.WhenToBuildTAStrategy wTBTA;
    TRSBounds.QuasiDetStrategy qDS;

    final int mCTR; // MAX_CONFLICTS_TO_RESOLVE
    final int mTOA; // MAX_TRANSITIONS_OF_A
    final int mSOA; // MAX_STATES_OF_A

    final boolean exportCertificate;

    @ParamsViaArgumentObject
    public QTRSRoofMatchBoundsTAProcessor(final Arguments arguments) {
        this.sTAS = arguments.sTAS;
        this.cRS = arguments.cRS;
        this.wTBTA = arguments.wTBTA;
        this.qDS = arguments.qDS;
        this.mCTR = arguments.MAX_CONFLICTS_TO_RESOLVE;
        this.mTOA = arguments.MAX_TRANSITIONS_OF_A;
        this.mSOA = arguments.MAX_STATES_OF_A;
        this.exportCertificate = arguments.exportCertificate;
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return true;
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {

        final Set<Rule> R = qtrs.getR();
        final boolean leftLinear = this.isLeftLinear(R);
        final boolean isNotDuplicating = this.isNonDuplicating(R);
        final boolean isRightlinear = CollectionUtils.isRightLinear(R);
        aborter.checkAbortion();

        boolean useRFC;
        if (this.exportCertificate) {
            useRFC = false;
        } else if (isRightlinear) {
            useRFC = true;
        } else {
            useRFC = false;
        }

        TRSBounds b = null;
        TRSBounds.Certificate certificate = null;
        if (leftLinear) {
            //create compatible TA
            if (isNotDuplicating) {
                b = new TRSBounds(R, TRSBounds.Bound.MATCH, this.sTAS, this.cRS, this.wTBTA, this.mCTR, this.mTOA, this.mSOA, useRFC);
            } else {
                b = new TRSBounds(R, TRSBounds.Bound.ROOF, this.sTAS, this.cRS, this.wTBTA, this.mCTR, this.mTOA, this.mSOA, useRFC);
            }
        } else {
            //create quasi-deterministic, raise-consistent, quasi-compatible TA
            if (isNotDuplicating) {
                b = new TRSBounds(R, TRSBounds.Bound.MATCHRAISE, this.sTAS, this.cRS, this.wTBTA, this.qDS, this.mCTR, this.mTOA, this.mSOA, useRFC);
            } else {
                b = new TRSBounds(R, TRSBounds.Bound.ROOFRAISE, this.sTAS, this.cRS, this.wTBTA, this.qDS, this.mCTR, this.mTOA, this.mSOA, useRFC);

            }

        }

        certificate = b.getCertificate(aborter);

        if (certificate != null) {
            return ResultFactory.proved(new QTRSRoofMatchBoundsTAProof(certificate));
        } else {
            return ResultFactory.unsuccessful();
        }
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

    public static class Arguments {
        public TRSBounds.STAStrategy sTAS = TRSBounds.STAStrategy.OSFEFS;
        public TRSBounds.ConflictResolvingStrategy cRS = TRSBounds.ConflictResolvingStrategy.NSFEPS;
        public TRSBounds.WhenToBuildTAStrategy wTBTA = TRSBounds.WhenToBuildTAStrategy.BUILD_TA_AFTER_RESOLVING_ONE_CONFLICT;
        public TRSBounds.QuasiDetStrategy qDS = TRSBounds.QuasiDetStrategy.APPROX;
        public int MAX_CONFLICTS_TO_RESOLVE = 10000;
        public int MAX_TRANSITIONS_OF_A = 10000;
        public int MAX_STATES_OF_A = 4000;
        public boolean exportCertificate = true;
    }

    /**
     * Proof of the bound processor
     *
     * @author CKuknat
     */
    private class QTRSRoofMatchBoundsTAProof extends QTRSProof {

        private final TRSBounds.Certificate certificate;

        public QTRSRoofMatchBoundsTAProof(final TRSBounds.Certificate certificate) {
            this.certificate = certificate;
        }

        /**
         * Returns the output string.
         * @author Marcel Klinzing
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {

            final StringBuilder result = new StringBuilder();
            String typeOfBound = "";

            if (this.certificate.getBound() == TRSBounds.Bound.ROOF || this.certificate.getBound() == TRSBounds.Bound.ROOFRAISE) {
                typeOfBound = "Roof-";
            } else if (this.certificate.getBound() == TRSBounds.Bound.MATCH || this.certificate.getBound() == TRSBounds.Bound.MATCHRAISE) {
                typeOfBound = "Match-";
            }
            if (this.certificate.getBound() == TRSBounds.Bound.ROOFRAISE || this.certificate.getBound() == TRSBounds.Bound.MATCHRAISE) {
                typeOfBound += "(raise-)";
            }

            result.append("The TRS R could be shown to be " + typeOfBound + "Bounded "
                + o.cite(new Citation[] {Citation.TAB_LEFTLINEAR, Citation.TAB_NONLEFTLINEAR }) + " by  " + this.certificate.getBoundedBy() + ". "
                + "Therefore it terminates.");

            /*result.append(o.linebreak());
            result.append(o.linebreak());
            result.append("The tree automaton used to show the " + typeOfBound + "Boundedness consists of "
                    + this.certificate.getTreeAutomaton().getTransitions()
                            .size()
                    + " transitions and of which there are "
                    + this.certificate.getTreeAutomaton().getEpsTransitions()
                            .size()
                    + " epsilon transitions and "
                    +
                + this.certificate.getTreeAutomaton().getAllStates().size() + " states.");*/

            result.append(o.linebreak());
            result.append(o.linebreak());
            result.append("The compatible tree automaton used to show the " + typeOfBound + "Boundedness is represented by: ");
            result.append(o.linebreak());
            this.certificate.printTA(o, result);

            return result.toString();
        }


        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (Globals.useAssertions) {
                assert (QTRSRoofMatchBoundsTAProcessor.this.exportCertificate);
            }
            return CPFTag.TRS_TERMINATION_PROOF.create(doc, this.certificate.toCPF(doc, xmlMetaData));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

}
