package aprove.verification.theoremprover.Simplifier;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A processor that takes a TRS and converts it to a SimplifierObligation contained
 * within a SimplifierProblem
 */
@NoParams
public class TRSToSimplifierProblem extends Processor.ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation o) {
        // applicable iff called with a TRS that has type information
        return (o instanceof TRS)
            && (((TRS)o).getProgram().getTypeContext()!=null);
    }





    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        Program prog = ((TRS)obl).getProgram();
        SimplifierObligation sObl = new SimplifierObligation(prog);
        SimplifierProblem simpl = new SimplifierProblem(sObl);
        return ResultFactory.proved(simpl, YNMImplication.EQUIVALENT, new TRStoSimplProof());
    }



    private static class TRStoSimplProof extends Proof.DefaultProof {
        private TRStoSimplProof() {
            this.shortName = "Create SimplifierProblem";
            this.longName = "Create Simplifier Problem from typed TRS";
        }

        @Override
        public String export (Export_Util o, VerbosityLevel level) {
            return "Created SimplifierProblem from TRS.";
        }
    }
}
