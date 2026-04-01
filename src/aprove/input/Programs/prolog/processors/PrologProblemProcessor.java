package aprove.input.Programs.prolog.processors;

import aprove.input.Programs.prolog.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * PrologProblemProcessor for processing PrologProblems.<br><br>
 *
 * Created: Sep 8, 2006<br>
 * Last modified: Nov 14, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class PrologProblemProcessor extends Processor.ProcessorSkeleton {

    /**
     * Process a PrologProblem.
     * @param pp The PrologProblem to process.
     * @param aborter The aborter for this processing.
     * @return The processed PrologProblem.
     * @throws AbortionException If the processing is aborted.
     */
    protected abstract Result processPrologProblem(PrologProblem pp, Abortion aborter) throws AbortionException;


    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#process(aprove.verification.dpframework.BasicObligation, aprove.NewObligations.ObligationNode, aprove.strategies.Abortions.Abortion, aprove.strategies.ExecutableStrategies.RuntimeInformation)
     */
    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        PrologProblem problem = (PrologProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getProgram().getClauses().isEmpty()) {
            return ResultFactory.proved(PrologProblemProcessor.ppIsEmptyProof);
        } else {
            return this.processPrologProblem(problem, aborter);
        }
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#isApplicable(aprove.verification.dpframework.BasicObligation)
     */
    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof PrologProblem) {
            return this.isPrologApplicable((PrologProblem) o);
        }
        return false;
    }

    /**
     * Tests whether or not the specified PrologProblem is applicable for
     * this PrologProblemProcessor.
     * @param pp The PrologProblem to test.
     * @return True, if the problem is applicable. False otherwise.
     */
    public abstract boolean isPrologApplicable(PrologProblem pp);

    /**
     * Proof for empty PrologPrograms.
     */
    private final static Proof ppIsEmptyProof = new PPisEmptyProof();

    /**
     * Proof for empty PrologPrograms.<br><br>
     *
     * Created: Sep 8, 2006<br>
     * Last modified: Oct 16, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    private static final class PPisEmptyProof extends Proof {

        /* (non-Javadoc)
         * @see aprove.Proofs.Proof.DefaultProof#export(aprove.verification.oldframework.Utility.Export_Util)
         */
        @Override
        public String export(Export_Util o) {
            return o.export("The Prolog program is empty. Hence, it trivially terminates.");
        }

    }

}
