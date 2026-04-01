package aprove.verification.dpframework.DPProblem.TheoremProver.TheoremProverRunners;

import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class AproveRunner implements TheoremProverRunner {

    @Override
    public Pair<Boolean, Exportable> runTheoremProverOnInput(
        final Formula frml,
        final Program prgrm,
        final String strategy,
        final String timeLimit,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        TheoremProverObligation.setMaxDepth(17);
        final TheoremProverObligation thmPrvrObl = new TheoremProverObligation(frml, prgrm);
        final BasicObligationNode tpoOblNode = new BasicObligationNode(thmPrvrObl);
        // start machine with new strategy
        final StrategyExecutionHandle handle =
            Machine.theMachine.startSubMachine(
                new VariableStrategy(strategy),
                rti.getProgram(),
                tpoOblNode,
                null,
                aborter.getClocks(),
                false);

        HandleChecker.check(handle, aborter);

        // okay, we have the result after the strategy
        return new Pair<Boolean, Exportable>(tpoOblNode.getTruthValue().equals(YNM.YES), new Exportable() {

            @Override
            public String toString() {
                return this.export(new PLAIN_Util());
            }

            @Override
            public String export(final Export_Util o) {
                final StringBuilder sb = new StringBuilder();
                //                sb.append("The following program was given to the internal theorem prover:");
                //                sb.append(o.linebreak());
                //                sb.append(o.preFormatted(prgrm.export(oo)));
                //                sb.append(o.linebreak());
                //                sb.append(o.linebreak());
                sb.append("The following output was given by the internal theorem prover:");
                sb.append(o.preFormatted(new ParallelPlainExportManager(tpoOblNode, "internal").export()));
                return sb.toString();
            }
        });
    }

}
