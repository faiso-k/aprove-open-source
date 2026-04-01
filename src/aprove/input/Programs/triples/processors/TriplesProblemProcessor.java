package aprove.input.Programs.triples.processors;

import aprove.input.Programs.triples.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author nowonder
 * @version $Id$
 */
public abstract class TriplesProblemProcessor implements Processor {

    protected abstract Result processTriplesProblem(
        TriplesProblem tp,
        Abortion aborter
    ) throws AbortionException;

    @Override
    public Result process(
        BasicObligation o,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        TriplesProblem problem = (TriplesProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getTriples().getClauses().isEmpty()) {
            return ResultFactory.proved(TriplesProblemProcessor.tpIsEmptyProof);
        } else {
            return this.processTriplesProblem(problem, aborter);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof TriplesProblem) {
            return this.isTriplesApplicable((TriplesProblem) o);
        }
        return false;
    }

    public abstract boolean isTriplesApplicable(TriplesProblem pp);

    /**
     * Proof for empty triples.
     */
    private final static Proof tpIsEmptyProof = new TPisEmptyProof();

    private static final class TPisEmptyProof extends Proof {

        @Override
        public String export(Export_Util o) {
            return o.export("There are no more dependency triples. Hence, the dependency triple problem trivially terminates.");
        }

    }

}
