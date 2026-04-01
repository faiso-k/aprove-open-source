package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class CdtKnowledgeProcessor extends CdtProblemProcessor {

    @Override
    protected boolean isCdtApplicable(final CdtProblem obl) {
        return !Options.certifier.isCpf();
    }

    @Override
    protected Result processCdt(final CdtProblem cdtProblem, final Abortion aborter)
            throws AbortionException {
        final Graph<Cdt, BitSet> graph = cdtProblem.getGraph().getGraph();
        final Set<Cdt> s = new LinkedHashSet<Cdt>(cdtProblem.getS());
        final Set<Cdt> k = new LinkedHashSet<Cdt>(cdtProblem.getK());
        final List<Cdt> removedFromS = new ArrayList<Cdt>();

        final ArrayDeque<Node<Cdt>> todo = new ArrayDeque<Node<Cdt>>();
        todo.addAll(graph.getNodesFromObjects(s));

        outer : while (!todo.isEmpty()) {
            final Node<Cdt> node = todo.poll();
            final Cdt cdt = node.getObject();
            if (k.contains(cdt)) {
                s.remove(cdt);
                removedFromS.add(cdt);
                continue;
            }

            final Set<Node<Cdt>> inNodes = graph.getIn(node);
            for (final Node<Cdt> inNode : inNodes) {
                if (!k.contains(inNode.getObject())) {
                    continue outer;
                }
            }
            s.remove(cdt);
            k.add(cdt);
            removedFromS.add(cdt);
            todo.addAll(graph.getOut(node));
        }

        if (removedFromS.isEmpty()) {
            return ResultFactory.unsuccessful("Could not propagate knowledge");
        } else if (s.isEmpty()) {
            return ResultFactory.provedWithValue(
                    ComplexityYNM.CONSTANT,
                    new CdtKnowledgeProof(removedFromS, true));
        } else {
            return ResultFactory.proved(
                    cdtProblem.createSubproblem(
                            cdtProblem.getGraph(),
                            ImmutableCreator.create(s),
                            ImmutableCreator.create(k)),
                    BothBounds.create(),
                    new CdtKnowledgeProof(removedFromS, false));
        }
    }

    public class CdtKnowledgeProof extends CpxProof {

        private final Collection<Cdt> removedFromS;
        private final boolean emptyS;

        public CdtKnowledgeProof(final Collection<Cdt> removedFromS, final boolean emptyS) {
            this.removedFromS = removedFromS;
            this.emptyS = emptyS;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(o.escape("The following tuples could be moved from S to K by knowledge propagation:"));
            sb.append(o.set(this.removedFromS, Export_Util.RULES));
            if (this.emptyS) {
                sb.append("Now S is empty");
            }
            return sb.toString();
        }

    }

}
