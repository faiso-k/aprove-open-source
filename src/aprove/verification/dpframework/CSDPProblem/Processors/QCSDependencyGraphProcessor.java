/**
 *
 */
package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Fabian Emmes <fabian.emmes@rwth-aachen.de>
 * @version $Id: QCSDependencyGraphProcessor.java,v 1.2 2007/11/22 10:04:10 fab
 *          Exp $
 */
@NoParams
public class QCSDependencyGraphProcessor extends QCSDPProcessor {

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem problem) {
        return true;
    }

    @Override
    public Result processQCSDP(QCSDPProblem problem, Abortion aborter)
            throws AbortionException {
        int nrSccs = 0;
        int nodes = 0;

        if (!problem.isGraphReducable()) {
            // Not applicable
            return ResultFactory.unsuccessful("Graph is not reducable");
        }

        Set<QCSDPProblem> problems = new LinkedHashSet<QCSDPProblem>();
        Set<QCSDependencyGraph> subgraphs = problem.getGraph()
                .getSccSubGraphs();
        for (QCSDependencyGraph graph : subgraphs) {
            ++nrSccs;
            nodes += graph.getNodes().size();
            aborter.checkAbortion();
            problems.add(QCSDPProblem.create(problem, graph));
        }

        int lessNodes = problem.getGraph().getNodes().size() - nodes;

        return ResultFactory.provedAnd(problems, YNMImplication.EQUIVALENT,
                new QCSDependencyGraphProof(problem.getGraph(), nrSccs,
                        lessNodes));
    }

    private class QCSDependencyGraphProof extends Proof.DefaultProof implements
            DOT_Able {

        private final QCSDependencyGraph dpGraph;

        private final int lessNodes;

        private final int nrSccs;

        public QCSDependencyGraphProof(QCSDependencyGraph dpGraph, int nrSccs,
                int lessNodes) {
            this.dpGraph = dpGraph;
            this.nrSccs = nrSccs;
            this.lessNodes = lessNodes;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            // TODO introduce citations
            s
                    .append("The approximation of the Context-Sensitive"
                            + " Dependency Graph " + o.cite(Citation.LPAR08)
                            + " contains " + this.nrSccs + " SCC"
                            + (this.nrSccs == 1 ? "" : "s"));
            if (this.lessNodes > 0) {
                s.append(" with " + this.lessNodes + " less node"
                        + (this.lessNodes == 1 ? "" : "s") + ".");
            } else {
                s.append(".");
            }
            s.append(o.cond_linebreak());
            s.append(this.dpGraph.export(o));
            return s.toString();
        }

        @Override
        public String toDOT() {
            return this.dpGraph.getGraph().toDOT();
        }
    }
}
