package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.xml.*;

@NoParams
public class DependencyGraphProcessor extends QDPProblemProcessor {

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        final QDependencyGraph graph = qdp.getDependencyGraph();
        // if ((Options.certifier.isCeta() || Options.certifier.isRainbow())
        // && !graph.isGenuineSCC()) {
        // // Make sure to always append a "Maybe(QDPNonSCC)" to this processor
        // // in all modes where this is enabled! Otherwise, you are going to
        // // experience infinite loops.
        // return true;
        // }
        return !graph.isSCC();
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {

        final QDependencyGraph graph = qdp.getDependencyGraph();

        final List<QDPProblem> resultObls = new ArrayList<>();

        final Set<Cycle<Rule>> sccs = graph.getGraph().getSCCs(false);
        if (graph.isSCC()) {
            // Since we already know from the applicability check that isGenuineSCC = false,
            // this means that we have a singleton node (should only occur in certain
            // certification modes).
            return ResultFactory.proved(qdp, YNMImplication.EQUIVALENT, new DependencyGraphProof(graph, 0, 0, qdp,
                resultObls, new LinkedList<Integer>(), new LinkedList<>(sccs)));
        }

        final Graph<Rule, ?> g = graph.getGraph();
        final Iterable<Cycle<Rule>> maybeRankedSccGraph;
        int iteratorSize = 0;
        if (Options.certifier.isCpf()) {
            // ugly hack
            final SCCGraph<Rule, ?> sccGraph = new SCCGraph<>(sccs, g);
            maybeRankedSccGraph = sccGraph.getRankedSCCs();
            iteratorSize = ((List<?>) maybeRankedSccGraph).size();
        } else {
            maybeRankedSccGraph = sccs;
            iteratorSize = sccs.size();
        }
        final Set<QDPProblem> newProblems = new LinkedHashSet<>();
        int size = 0;

        final LinkedList<Integer> nonSccs = new LinkedList<>();
        int iterator = 0;
        for (final Cycle<Rule> rankedScc : maybeRankedSccGraph) {
            iterator++;
            final QDependencyGraph subScc = graph.getSubGraph(rankedScc);
            if (subScc.isGenuineSCC()) {
                final QDPProblem newProblem = qdp.getSubProblem(subScc);
                newProblems.add(newProblem);
                resultObls.add(newProblem);
                size += newProblem.getP().size();
            } else {
                nonSccs.add(iteratorSize - iterator + 1);
            }
        }
        final int lessNodes = qdp.getP().size() - size;
        final int nrSccs = newProblems.size();

        final Result result =
            ResultFactory.provedAnd(newProblems, YNMImplication.EQUIVALENT, new DependencyGraphProof(graph, nrSccs,
                lessNodes, qdp, resultObls, nonSccs, maybeRankedSccGraph));
        return result;

    }

    public static class DependencyGraphProof extends QDPProof implements DOT_Able {

        private final QDependencyGraph graph;
        private final int nrSccs;
        private final int lessNodes;
        private final BasicObligation origObl;
        private final List<QDPProblem> resultObls;
        private final LinkedList<Integer> nonSccs;
        private final Iterable<Cycle<Rule>> rankedSccGraph;

        private DependencyGraphProof(final QDependencyGraph graph, final int nrSccs, final int lessNodes,
                final BasicObligation origObl, final List<QDPProblem> resultObls,
                final LinkedList<Integer> nonSccs, final Iterable<Cycle<Rule>> rankedSccGraph) {
            this.graph = graph;
            this.nrSccs = nrSccs;
            this.lessNodes = lessNodes;
            this.origObl = origObl;
            this.resultObls = resultObls;
            this.nonSccs = nonSccs;
            this.rankedSccGraph = rankedSccGraph;
        }

        private static final Citation[] citations = new Citation[] {Citation.LPAR04, Citation.FROCOS05,
            Citation.EDGSTAR };

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res =
                "The approximation of the Dependency Graph " + o.cite(DependencyGraphProof.citations) + " contains " + this.nrSccs + " SCC"
                    + (this.nrSccs == 1 ? "" : "s");
            if (this.lessNodes > 0) {
                res += " with " + this.lessNodes + " less node" + (this.lessNodes == 1 ? "" : "s") + ".";
            } else {
                res += ".";
            }
            return o.export(res);
        }

        @Override
        public String toDOT() {
            return this.graph.toDOT();
        }

        @Override
        @SuppressWarnings("unchecked")
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                final Graph<Rule, Object> g = (Graph<Rule, Object>) (this.graph.getGraph());
                int count = 0;
                final List<Element> components = new ArrayList<Element>();
                for (final Cycle<Rule> rankedScc : this.rankedSccGraph) {
                    boolean isGenuine = false;

                    // easiest way to check genuinity + checking if it has a edge to itself
                    if (rankedScc.size() > 1 || rankedScc.hasDirectEdgeTo(rankedScc, g)) {
                        isGenuine = true;
                    }

                    final Element component = CPFTag.COMPOMENT.createElement(doc);
                    final Element dps = CPFTag.DPS.createElement(doc);
                    final Element rules = CPFTag.RULES.createElement(doc);
                    final Element realScc = CPFTag.REAL_SCC.createElement(doc);
                    realScc.appendChild(doc.createTextNode(isGenuine ? "true" : "false"));

                    for (final Rule rule : rankedScc.getNodeObjects()) {
                        rules.appendChild(rule.toCPF(doc, xmlMetaData));
                    }
                    dps.appendChild(rules);
                    component.appendChild(dps);
                    component.appendChild(realScc);
                    if (isGenuine) {
                        component.appendChild(childrenProofs[count]);
                        count++;
                    }
                    components.add(component);
                }
                final Element proof = CPFTag.DEP_GRAPH_PROC.createElement(doc);
                final int n = components.size(); // add components in reverse order
                for (int i = n - 1; i >= 0; i--) {
                    proof.appendChild(components.get(i));
                }

                return CPFTag.DP_PROOF.create(doc, proof);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultObls.get(modus.negativeReason()));
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }

}
