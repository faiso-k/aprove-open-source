package aprove.verification.dpframework.PADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PADPProblem.Utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

@NoParams
public class CSPADPEDGProcessor extends CSPADPProcessor {

    @Override
    protected Result processCSPADP(CSPADPProblem cspadp, Abortion aborter) throws AbortionException {
        CSPAEDG graph = CSPAEDG.create(cspadp, aborter);

        if (graph.isSCC()) {
            return ResultFactory.unsuccessful();
        }

        Set<CSPADPProblem> sccs = new LinkedHashSet<CSPADPProblem>(graph.getSCCs());

        int size = 0;
        for (CSPADPProblem scc : sccs) {
            size += scc.getP().size();
        }

        int lessNodes = cspadp.getP().size() - size;
        int nrSccs = sccs.size();

        return ResultFactory.provedAnd(sccs, YNMImplication.EQUIVALENT, new CSPADPEDGProof(graph, nrSccs, lessNodes));
    }

    private static class CSPADPEDGProof extends Proof.DefaultProof implements DOT_Able {

        private final CSPAEDG graph;
        private final int nrSccs;
        private final int lessNodes;

        private CSPADPEDGProof(CSPAEDG graph, int nrSccs, int lessNodes) {
            this.graph = graph;
            this.nrSccs = nrSccs;
            this.lessNodes = lessNodes;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res = "The approximation of the context-sensitive PA Dependency Graph has " + this.nrSccs + " SCC" + (this.nrSccs == 1 ? "" : "s");
            if (this.lessNodes > 0) {
                res += " containing " + this.lessNodes + " node"+ (this.lessNodes == 1 ? "" : "s") + " less than P.";
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
