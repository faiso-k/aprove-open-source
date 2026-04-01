package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * checks whether the TRS R is RFC-matchbounded
 */
public class RFCMatchBoundsProcessor extends QTRSProcessor {

    private final static Logger logger = Logger.getLogger("aprove.verification.dpframework.TRSProblems.Processors.RFCMatchBoundsProcessor");

    private final int nodeBound;
    private final int edgeBound;

    @ParamsViaArgumentObject
    public RFCMatchBoundsProcessor(final Arguments arguments) {
        this.edgeBound = arguments.edgeBound;
        this.nodeBound = arguments.nodeBound;
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        // check that R is maxUnary
        for (final FunctionSymbol f : qtrs.getRSignature()) {
            if (f.getArity() > 1) {
                return false;
            }
        }
        return true;
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {

        final Set<Rule> R = qtrs.getR();

        if (Globals.DEBUG_COTTO) {
            if (RFCMatchBoundsProcessor.logger.isLoggable(Level.FINE)) {
                RFCMatchBoundsProcessor.logger.log(Level.FINE, "RFC working on Rules: \n");
                for (final Rule rule : R) {
                    RFCMatchBoundsProcessor.logger.log(Level.FINE, rule + "\n");
                }
            }
        }

        final MatchBound<?> mb = new MatchBound<Object>(R, qtrs.getRSignature(), qtrs.getSignature(), this.nodeBound, this.edgeBound);
        aborter.checkAbortion();
        final CertificateGraph<?> certificate = mb.getCertificate(aborter);
        if (certificate != null) {
            final int matchBound = mb.getMatchBound();
            if (Globals.DEBUG_COTTO) {
                RFCMatchBoundsProcessor.logger.log(Level.INFO, "MatchBound: " + matchBound + "\n");
            }
            return ResultFactory.proved(new RFCMatchBoundsTRSProof(qtrs, certificate, matchBound));
        } else {
            return ResultFactory.unsuccessful();
        }
    }



    public static class RFCMatchBoundsTRSProof extends QTRSProof implements DOT_Able {

        /**
         * The TRS that is match-bounded
         */
        private final QTRSProblem qtrs;

        /**
         * The graph representing the certificate generated for the proof
         */
        private final CertificateGraph certificate;

        /**
         * The match bound found (highest annotation of all edges labeled
         * with <code>AnnotatedFunctionSymbols</code> in the graph)
         */
        private final int matchBound;

        /**
         * Creates a new <code>RFCMatchBoundsTRSProof</code> instance.
         *
         * @param trs the <code>TRS</code> for which a certificate was
         * constructed
         * @param certificate the graph representing the certificate
         * @param matchBound the match bound found
         */
        public RFCMatchBoundsTRSProof(final QTRSProblem qtrs, final CertificateGraph certificate, final int matchBound) {

            this.certificate = certificate;
            this.matchBound = matchBound;
            this.qtrs = qtrs;

        }

        /**
         * Formats the output string of the proof and returns it.
         *
         * @param o an <code>Export_Util</code> value, used to format the
         * proof, according to the chosen output method
         * @return a <code>String</code>, giving a human readable
         * representation of this proof
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();

            result.append("Termination of the TRS R could be shown with a Match Bound "+o.cite(new Citation[]{Citation.MATCHBOUNDS1, Citation.MATCHBOUNDS2})+" of " + this.matchBound + ". ");
            result.append("This implies Q-termination of R.");
            result.append(o.linebreak());

            result.append("The following rules were used to construct the certificate:");
            result.append(o.linebreak());
            result.append(o.set(this.qtrs.getR(), Export_Util.RULES));
            result.append(o.linebreak());

            result.append("The certificate found is represented by the following graph.");
            result.append(o.cond_linebreak());
            result.append(o.export(this.certificate));
            result.append(o.cond_linebreak());


            return result.toString();
        }

        @Override
        public String toDOT() {
            return this.certificate.toInteractiveDOTwithEdges();
        }

    }

    public static class Arguments {
        public int edgeBound = 120;
        public int nodeBound = 90;
    }

}
