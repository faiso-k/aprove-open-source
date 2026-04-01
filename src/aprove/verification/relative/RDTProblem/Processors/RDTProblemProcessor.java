package aprove.verification.relative.RDTProblem.Processors;

import org.w3c.dom.*;

import aprove.cli.ObligationCache.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.relative.RDTProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

/**
 * General skeleton of an arbitrary RDTProblem processor
 * 
 * @author Grigory Vartanyan
 * @version $Id$
 */
public abstract class RDTProblemProcessor extends Processor.ProcessorSkeleton {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof RDTProblem) {
            return this.isRDTPApplicable((RDTProblem) o);
        }
        return false;
    }

    /**
     * Check whether this processor is applicable to the PQDPProblem
     * @return
     */
    public abstract boolean isRDTPApplicable(RDTProblem rdpp);

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter,
            final RuntimeInformation rti) throws AbortionException {
        final RDTProblem problem = (RDTProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getD1().isEmpty()) {
            return ResultFactory.proved(RDTProblemProcessor.dAbsIsEmptyProof);
        }
        if (BasicObligationCache.oblCache != null) {
            final YNM value = (YNM) BasicObligationCache.oblCache.lookup(problem);
            if (value != null) {
                switch (value) {
                    case YES:
                        return ResultFactory.proved(RDTProblemProcessor.rIsCachedProof);
                    case NO:
                        return ResultFactory.disproved(RDTProblemProcessor.rIsCachedProof);
                }
            }
            oblNode.addTruthValueListener(
                    new BasicObligationCache.CacheTruthValueListener(BasicObligationCache.oblCache, o));
        }
        return this.processRDTProblem(problem, aborter);
    }

    /**
     * Process a RDPProblem with a non-empty set of dependency pairs
     * @return
     */
    protected abstract Result processRDTProblem(RDTProblem pqdp, Abortion aborter) throws AbortionException;

    // ================================================================================
    // Predefined Proofs
    // ================================================================================

    final static DAbsisEmptyProof dAbsIsEmptyProof = new DAbsisEmptyProof();

    private static final class DAbsisEmptyProof extends RDTProof {

        @Override
        public String export(final Export_Util o, VerbosityLevel level) {
            return o.export("The RDT Problem has an empty D_abs. Hence, no infinite chain exists.");
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
            return o.export("This RDT Problem has been analyzed before.");
        }

        public String toBibTeX() {
            return "";
        }

    }

}
