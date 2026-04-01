package aprove.input.Programs.prolog.processors;

import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

public class PrologToGraphProcessor extends PrologGraphProcessor {

    @ParamsViaArgumentObject
    public PrologToGraphProcessor(final PrologOptions args) {
        super(args);
    }

    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologToGraphProcessor");

    @Override
    protected Logger getLogger() {
        return PrologToGraphProcessor.log;
    }

    @Override
    protected Result processGraph(PrologEvaluationGraph graph, Abortion aborter) throws AbortionException {
        return ResultFactory.proved(new PrologGraphProblem(graph), YNMImplication.SOUND, new PrologToGraphProof());
    }

    @Override
    public boolean isPrologApplicable(PrologProblem pp) {
        return true;
    }

    private class PrologToGraphProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Created Symbolic Evaluation Graph for Prolog program.";
        }

    }

}
