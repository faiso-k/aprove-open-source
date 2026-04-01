package aprove.verification.relative.RelADPProblem.Processors;

import org.w3c.dom.*;

import aprove.cli.ObligationCache.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.relative.RelADPProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

/**
 * General skeleton of an arbitrary relative ADPProblem processor
 * 
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public abstract class RelADPProblemProcessor extends Processor.ProcessorSkeleton {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof RelADPProblem) {
            return this.isRelADPPApplicable((RelADPProblem) o);
        }
        return false;
    }

    /**
     * Check whether this processor is applicable to the PQDPProblem
     * @return
     */
    public abstract boolean isRelADPPApplicable(RelADPProblem reladpp);

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter,
            final RuntimeInformation rti) throws AbortionException {
        final RelADPProblem problem = (RelADPProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getPAbs().isEmpty()) {
            return ResultFactory.proved(RelADPProblemProcessor.dAbsIsEmptyProof);
        }
        if (BasicObligationCache.oblCache != null) {
            final YNM value = (YNM) BasicObligationCache.oblCache.lookup(problem);
            if (value != null) {
                switch (value) {
                    case YES:
                        return ResultFactory.proved(RelADPProblemProcessor.rIsCachedProof);
                    case NO:
                        return ResultFactory.disproved(RelADPProblemProcessor.rIsCachedProof);
                }
            }
            oblNode.addTruthValueListener(
                    new BasicObligationCache.CacheTruthValueListener(BasicObligationCache.oblCache, o));
        }
        return this.processRelADPProblem(problem, aborter);
    }

    /**
     * Process a RDPProblem with a non-empty set of dependency pairs
     * @return
     */
    protected abstract Result processRelADPProblem(RelADPProblem pqdp, Abortion aborter) throws AbortionException;

    // ================================================================================
    // Predefined Proofs
    // ================================================================================

    final static DAbsisEmptyProof dAbsIsEmptyProof = new DAbsisEmptyProof();

    private static final class DAbsisEmptyProof extends RelADPProof {

        @Override
        public String export(final Export_Util o, VerbosityLevel level) {
            return o.export("The relative ADP Problem has an empty P_abs. Hence, no infinite chain exists.");
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData,
                final CPFModus modus) {
            return CPFTag.DT_PROOF.create(doc,
                    CPFTag.D_ABS_IS_EMPTY.create(doc));  // TODO: change
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }

    private final static Proof rIsCachedProof = new RisCachedProof();

    private static final class RisCachedProof extends Proof {

        @Override
        public String export(final Export_Util o) {
            return o.export("This relative ADP Problem has been analyzed before.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
