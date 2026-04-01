package aprove.verification.theoremprover.TerminationProcedures;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.TRSProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

/**
 * Converts an equational TRS (e.g., coming from the parser for AProVE's
 * classic TES input language) to an ETRSProblem.
 *
 * @author Carsten Fuhs
 */
@NoParams
public class ETESToETRSProcessor extends TRSProcessor {

     @Override
    protected Result processProgram(TRS trs, Abortion aborter) throws AbortionException {
         ImmutableSet<Rule> R = ImmutableCreator.create(trs.getProgram().getNewRules());
         ImmutableSet<Equation> E = ImmutableCreator.create(trs.getProgram().getNewEquations());
         ETRSProblem etrs = ETRSProblem.create(R, E);
         return ResultFactory.proved(etrs, YNMImplication.EQUIVALENT, new ETESToETRSProof());
     }

     @Override
    public boolean isEquationalAble() {
         return true;
     }

     private static class ETESToETRSProof extends Proof {
         @Override
        public String export(Export_Util o) {
             StringBuilder s = new StringBuilder();
             s.append(o.export("Transformed ETES into ETRS."));
             s.append(o.cond_linebreak());
             return s.toString();
         }
     }
}
