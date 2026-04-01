package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * checks whether the TRS R is RFC-matchbounded
 */
public class RFCMatchBoundsProcessor extends QDPProblemProcessor {

    private final  static Logger logger = Logger.getLogger("aprove.verification.dpframework.TRSProblems.Processors.RFCMatchBoundsProcessor");
    private final int nodeBound;
    private final int edgeBound;

    @ParamsViaArgumentObject
    public RFCMatchBoundsProcessor(final Arguments arguments) {
        this(arguments.nodeBound, arguments.edgeBound);
    }

    public RFCMatchBoundsProcessor(final int nodeBound, final int edgeBound) {
        this.nodeBound = nodeBound;
        this.edgeBound = edgeBound;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        // check that P cup R is maxUnary
        for (final FunctionSymbol f : qdp.getPRSignature()) {
            if (f.getArity() > 1) {
                return false;
            }
        }
        return true;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {

        final boolean minimal = qdp.getMinimal();
        Set<Rule> initRules = null;
        if (minimal) {
            initRules = qdp.getP();
        }

        final Set<Rule> matchingRules = new LinkedHashSet<Rule>(qdp.getR());
        matchingRules.addAll(qdp.getP());

        if (Globals.DEBUG_COTTO) {
            if (RFCMatchBoundsProcessor.logger.isLoggable(Level.FINE)) {
                RFCMatchBoundsProcessor.logger.log(Level.FINE, "RFC working on Rules: \n");
                for (final Rule rule : matchingRules) {
                    RFCMatchBoundsProcessor.logger.log(Level.FINE, rule + "\n");
                }
            }
        }

        MatchBound<?> mb;
        if (minimal) {
            mb = new MatchBound<Object>(initRules, matchingRules, qdp.getPRSignature(), qdp.getSignature(), this.nodeBound, this.edgeBound);
        } else {
            mb = new MatchBound<Object>(matchingRules, qdp.getPRSignature(), qdp.getSignature(), this.nodeBound, this.edgeBound);
        }
        aborter.checkAbortion();
        final CertificateGraph<?> certificate = mb.getCertificate(aborter);
        if (certificate != null) {
            final int matchBound = mb.getMatchBound();
            if (Globals.DEBUG_COTTO) {
                RFCMatchBoundsProcessor.logger.log(Level.INFO, "MatchBound: " + matchBound);
            }
            return ResultFactory.proved(new RFCMatchBoundsDPProof(initRules, matchingRules, certificate, matchBound, qdp));
        } else {
            return ResultFactory.unsuccessful();
        }
    }



    public static class RFCMatchBoundsDPProof extends QDPProof implements DOT_Able {

        /**
         * the rules that where used for the matching
         */
        private final Set<Rule> matchingRules;

        /**
         * the rules that where used for initializing the graph
         */
        private final Set<Rule> initRules;

        /**
         * The graph representing the certificate generated for the proof
         */
        private final CertificateGraph certificate;

        /**
         * The match bound found (highest annotation of all edges labeled
         * with <code>AnnotatedFunctionSymbols</code> in the graph)
         */
        private final int matchBound;

        private final QDPProblem origQDP;

        /**
         * Creates a new <code>RFCMatchBoundsTRSProof</code> instance.
         *
         * @param trs the <code>TRS</code> for which a certificate was
         * constructed
         * @param certificate the graph representing the certificate
         * @param matchBound the match bound found
         */
        public RFCMatchBoundsDPProof(final Set<Rule> initRules, final Set<Rule> matchingRules, final CertificateGraph certificate, final int matchBound,
                final QDPProblem origQDP) {

            this.certificate = certificate;
            this.matchBound = matchBound;
            this.matchingRules = matchingRules;
            this.initRules = initRules;
            this.origQDP = origQDP;

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
            final StringBuffer result = new StringBuffer();

            if (this.initRules == null) {
                result.append("Termination of the TRS P cup R can be shown by a matchbound "+o.cite(new Citation[]{Citation.MATCHBOUNDS1, Citation.MATCHBOUNDS2})+" of "+this.matchBound+". " +
                    "This implies finiteness of the given DP problem.");
                result.append(o.cond_linebreak());
                result.append("The following rules (P cup R) were used to construct the certificate:");
                result.append(o.linebreak());
                result.append(o.set(this.matchingRules, Export_Util.RULES));
                result.append(o.cond_linebreak());
            } else {
                result.append("Finiteness of the DP problem can be shown by a matchbound of "+this.matchBound+". ");
                result.append(o.linebreak());

                result.append("As the DP problem is minimal we only have to initialize the certificate graph by the rules of P:");
                result.append(o.linebreak());
                result.append(o.set(this.initRules, Export_Util.RULES));
                result.append(o.cond_linebreak());

                result.append("To find matches we regarded all rules of R and P:");
                result.append(o.linebreak());
                result.append(o.set(this.matchingRules, Export_Util.RULES));
                result.append(o.cond_linebreak());
            }

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

    public static class Arguments{
        public int nodeBound = 90;
        public int edgeBound = 120;
    }

}
