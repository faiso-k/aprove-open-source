package aprove.input.Programs.llvm.processors;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * This processor takes a LLVM graph and splits it into SCCs which can
 * be analyzed on their own.
 */
public class LLVMSEGraphToSCCProcessor extends Processor.ProcessorSkeleton {

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#isApplicable(aprove.prooftree.Obligations.BasicObligation)
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof LLVMSEGraphProblem);
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.Processor#process(aprove.prooftree.Obligations.BasicObligation, aprove.prooftree.Obligations.BasicObligationNode, aprove.strategies.Abortions.Abortion, aprove.strategies.ExecutableStrategies.RuntimeInformation)
     */
    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti
    ) throws AbortionException {
        final LLVMSEGraph graph = ((LLVMSEGraphProblem) obl).getGraph();
        if (Globals.DEBUG_MARC) {
            graph.dumpGraph();
        }
        final LinkedList<LLVMSCCProblem> problems = new LinkedList<LLVMSCCProblem>();
        final LinkedHashSet<Cycle<LLVMAbstractState>> sccs = graph.getSCCs();
        for (final Cycle<LLVMAbstractState> s : sccs) {
            problems.add(new LLVMSCCProblem(graph.getSubGraph(s), false));
        }
        return
            ResultFactory.provedAnd(
                problems,
                YNMImplication.SOUND,
                new SymbolicExecutionGraphToSCCProof(problems.size())
            );
    }

    /**
     * A very fine proof.
     * @author Marc Brockschmidt
     */
    public class SymbolicExecutionGraphToSCCProof extends DefaultProof {

        /**
         * How many SCCs were constructed
         */
        private final int sccNumber;

        /**
         * @param sccN number of separate SCCs.
         */
        public SymbolicExecutionGraphToSCCProof(final int sccN) {
            super();
            this.sccNumber = sccN;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Utility.VerbosityExportable#export(aprove.prooftree.Export.Utility.Export_Util, aprove.verification.oldframework.Utility.VerbosityLevel)
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            if (this.sccNumber == 0) {
                return "Proven termination by absence of SCCs";
            } else {
                return
                    "Splitted symbolic execution graph to "
                    + this.sccNumber
                    + " SCC"
                    + ((this.sccNumber > 1) ? "s." : ".");
            }
        }

    }

}
