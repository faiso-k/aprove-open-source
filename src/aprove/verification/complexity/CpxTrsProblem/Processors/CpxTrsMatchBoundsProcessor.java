package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.complexity.Utility.RCMatchBounds.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

public class CpxTrsMatchBoundsProcessor extends RuntimeComplexityTrsProcessor {

    private final static ComplexityYNM linear = ComplexityYNM.create(ComplexityValue.constant(), ComplexityValue.linear());
    private final Arguments arguments;

    @ParamsViaArgumentObject
    public CpxTrsMatchBoundsProcessor(final Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public boolean isRuntimeComplexityTrsApplicable(final RuntimeComplexityTrsProblem obl) {
        // check that the problem is at most unary
        for (final FunctionSymbol f : obl.getSignature()) {
            if (f.getArity() > 1) {
                return false;
            }
        }
        if (Options.certifier.isCpf() && Rule.isCollapsing(obl.getR())) {
            // there is some special treatment of collapsing rules
            // (they are expanded into several non-collapsing ones)
            // which is not covered by the standard criterion of closure of L(A) under match(R)
            // -> these proofs are not CPF-conform
            return false;
        }
        return true;
    }

    private final static Logger logger =
        Logger.getLogger("aprove.verification.complexity.CpxTrsProblem.Processors.CpxTrsMatchBoundsProcessor");

    @Override
    public Result processRuntimeComplexityTrs(final RuntimeComplexityTrsProblem cpxTrs, final Abortion aborter) throws AbortionException {

        final Set<Rule> R = cpxTrs.getR();
        if (Options.certifier.isCpf()) { // no string reversal for CPF
            // it is ugly anyway to integrate string reversal into matchbounds,
            // why isn't this a separate processor?
            this.arguments.reversed = false;
        }
        if (Options.certifier.isCeta()) {
            // CeTA's containment check does not cover the splitEnds construction
            this.arguments.splitEnds = false;
        }
        final RCMatchBounds mb = new RCMatchBounds(R, this.arguments);
        CertificateGraph certificate;
        try {
            certificate = mb.getCertificate(aborter);
        } catch (final LimitExceededException e) {
            return ResultFactory.unsuccessful(e.getMessage());
        }

        if (certificate != null) {
            final int matchBound = certificate.getMatchBound();
            CpxTrsMatchBoundsProcessor.logger.log(Level.INFO, "MatchBound: " + matchBound + "\n");
            final boolean cpfAble = !this.arguments.splitEnds && !this.arguments.reversed && !Rule.isCollapsing(R);
            return ResultFactory.provedWithValue(CpxTrsMatchBoundsProcessor.linear, new CpxTrsMatchBoundsProof(
                cpxTrs,
                certificate,
                matchBound,
                cpfAble));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    public static class CpxTrsMatchBoundsProof extends CpxProof implements DOT_Able {

        /**
         * The TRS that is match-bounded
         */
        private final RuntimeComplexityTrsProblem cpxTrs;

        /**
         * The graph representing the certificate generated for the proof
         */
        private final CertificateGraph certificate;

        /**
         * The match bound found (highest annotation of all edges labeled with
         * <code>AnnotatedFunctionSymbols</code> in the graph)
         */
        private final int matchBound;

        private final boolean cpfAble; // indicate whether this proof is exportable to CPF

        /**
         * Creates a new <code>MatchBoundsTRSProof</code> instance.
         * @param trs the <code>TRS</code> for which a certificate was
         * constructed
         * @param certificate the graph representing the certificate
         * @param matchBound the match bound found
         */
        public CpxTrsMatchBoundsProof(
            final RuntimeComplexityTrsProblem cpxTrs,
            final CertificateGraph certificate,
            final int matchBound,
            final boolean cpfAble)
        {

            this.certificate = certificate;
            this.matchBound = matchBound;
            this.cpxTrs = cpxTrs;
            this.cpfAble = cpfAble;

        }

        /**
         * Formats the output string of the proof and returns it.
         * @param o an <code>Export_Util</code> value, used to format the proof,
         * according to the chosen output method
         * @return a <code>String</code>, giving a human readable representation
         * of this proof
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuffer result = new StringBuffer();

            result.append("A linear upper bound on the runtime complexity of the TRS R could be shown with a Match Bound "
                + o.cite(new Citation[] { Citation.MATCHBOUNDS1, Citation.MATCHBOUNDS2 })
                + " of "
                + this.matchBound
                + ". ");
            result.append(o.linebreak());

            /*
            result.append("The following rules were used to construct the certificate:");
            result.append(o.linebreak());
            result.append(o.set(this.cpxTrs.getR(), Export_Util.RULES));
            result.append(o.linebreak());
            */

            /*
            result.append("\nMATCHBOUND:" + this.certificate.getMatchBound() + "\t");
            result.append("NODES:" + this.certificate.getNumNodes() + "\t");
            result.append("ITERATIONS:" + this.certificate.getIteration() + "\t");
            result.append("REVERSED:" + this.certificate.isReversed() + "\t");
            result.append("SPLITENDS:" + this.certificate.isSplitEnds() + "\t");
            result.append("FORWARD:" + this.certificate.isForwardScan() + "\t");
            result.append("BACKWARD:" + this.certificate.isBackwardScan() + "\n");
            result.append(o.linebreak());
            */

            result.append("The certificate found is represented by the following graph." + o.newline());
            result.append(o.quote(o.export(this.certificate)));

            return result.toString();
        }

        @Override
        public String toDOT() {
            return this.certificate.toInteractiveDOTwithEdges();
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
            return this.cpfAble;
        }

    }

    public static class Arguments {
        public boolean reversed = false;
        public boolean splitEnds = false;
        public boolean forwardScan = true;
        public boolean backwardScan = true;
        public int maxMatchBound = 7; // maximum seen 6
        public int maxNodes = 20000; // maximum seen 18020
        public int maxIterations = 30; // maximum seen 25
    }

}
