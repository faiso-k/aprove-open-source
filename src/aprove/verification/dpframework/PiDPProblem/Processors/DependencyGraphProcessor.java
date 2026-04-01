package aprove.verification.dpframework.PiDPProblem.Processors;


import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

@NoParams
public class DependencyGraphProcessor extends PiDPProblemProcessor {

    @Override
    public boolean isPiDPApplicable(AbstractPiDPProblem apidp) {
        return !apidp.getDependencyGraph().isSCC();
    }


    @Override
    protected Result processPiDPProblem(AbstractPiDPProblem apidp,
        Abortion aborter) throws AbortionException {

        PiDependencyGraph graph = apidp.getDependencyGraph();
        Set<PiDependencyGraph> subSccs = graph.getSubSCCs();

        Set<AbstractPiDPProblem> newProblems =
            new LinkedHashSet<AbstractPiDPProblem>();
        int size = 0;
        for (PiDependencyGraph subScc : subSccs) {
            Set<? extends AbstractPiDPProblem> subProblems =
                apidp.getSubProblems(subScc);
            for (AbstractPiDPProblem newProblem : subProblems) {
                newProblems.add(newProblem);
            }
            //size += newProblem.getP().size();
            size += subScc.getP().size();
        }

        int lessNodes = apidp.getP().size() - size;
        int nrSccs = newProblems.size();

        Result result = ResultFactory.provedAnd(newProblems, YNMImplication.EQUIVALENT, new DependencyGraphProof(graph, nrSccs, lessNodes));
        return result;

    }

    private static class DependencyGraphProof extends Proof.DefaultProof implements DOT_Able {

        private final PiDependencyGraph graph;
        private final int nrSccs;
        private final int lessNodes;

        private DependencyGraphProof(PiDependencyGraph graph, int nrSccs, int lessNodes) {
            this.graph = graph;
            this.nrSccs = nrSccs;
            this.lessNodes = lessNodes;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res = "The approximation of the Dependency Graph "+o.cite(Citation.LOPSTR)+" contains " + this.nrSccs + " SCC" + (this.nrSccs == 1 ? "" : "s");
            if (this.lessNodes > 0) {
                res += " with " + this.lessNodes + " less node"+ (this.lessNodes == 1 ? "" : "s") + ".";
            } else {
                res += ".";
            }
            return o.export(res);
        }

        @Override
        public String toDOT() {
            return this.graph.toDOT();
        }
    }

}
