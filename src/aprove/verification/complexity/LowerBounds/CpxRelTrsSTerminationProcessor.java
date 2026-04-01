package aprove.verification.complexity.LowerBounds;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/*
 * Tries to prove innermost termination of S.
 */
public class CpxRelTrsSTerminationProcessor extends CpxRelTrsProcessor {

    @Override
    protected Result processCpxRelTrs(CpxRelTrsProblem obl, Abortion aborter, RuntimeInformation rti) {
        if (!obl.getS().isEmpty()) {
            ImmutableSet<aprove.verification.dpframework.BasicStructures.Rule> relativeRules = obl.getS();
            QTRSProblem newObl = QTRSProblem.create(relativeRules).createInnermost();
            StrategyExecutionHandle handle = Machine.theMachine.startSubMachine(null, rti.getProgram(), new BasicObligationNode(newObl), null, aborter.getClocks(), false);
            HandleChecker.check(handle, aborter);
            if (newObl.getTruthValue() != YNM.YES) {
                return ResultFactory.unsuccessful();
            }
        }
        return ResultFactory.proved(obl.provedTerminationOfS(), BothBounds.forConcreteBounds(), new SInnermostTerminationProof());
    }

    @Override
    protected boolean isCpxRelTrsApplicable(CpxRelTrsProblem obl) {
        return !obl.STerminatesInnermost() && Options.certifier.isNone();
    }

    public static class SInnermostTerminationProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "proved innermost termination of relative rules";
        }

    }

}
