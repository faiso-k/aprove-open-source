/*
 * Created on Feb 1, 2006
 */
package aprove.verification.dpframework.DPProblem.Processors;

/**
 * @author stein
 * @version $Id$
 */

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
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
public class EDependencyGraphProcessor extends EDPProblemProcessor {

    @Override
    public boolean isEDPApplicable(EDPProblem edp) {
        return !edp.getDependencyGraph().isSCC();
    }


    @Override
    protected Result processEDPProblem(EDPProblem edp, Abortion aborter) throws AbortionException {

        EDependencyGraph graph = edp.getDependencyGraph();
        Set<EDependencyGraph> subSccs = graph.getSubSCCs();

        Collection<EDPProblem> newProblems = new ArrayList<EDPProblem>();
        int size = 0;
        for (EDependencyGraph subScc : subSccs) {
            aborter.checkAbortion();
            EDPProblem newProblem = edp.getSubProblem(subScc);
            newProblems.add(newProblem);
            size += newProblem.getP().size();
        }

        int lessNodes = edp.getP().size() - size;
        int nrSccs = newProblems.size();
        
        final Graph<HasTermPair, ?> g = graph.getGraph();
        final Set<Cycle<HasTermPair>> sccs = g.getSCCs(false);

        Result result = ResultFactory.provedAnd(
        		newProblems, 
        		YNMImplication.EQUIVALENT, 
        		new EDependencyGraphProof(
        			graph, 
        			nrSccs, 
        			lessNodes,
        			sccs));
        return result;

    }

    private static class EDependencyGraphProof extends Proof.DefaultProof implements DOT_Able {

        private final EDependencyGraph graph;
        private final int nrSccs;
        private final int lessNodes;
        private final Iterable<Cycle<HasTermPair>> rankedSccGraph;


        private EDependencyGraphProof(EDependencyGraph graph, int nrSccs, int lessNodes,
        	Iterable<Cycle<HasTermPair>> rankedSccGraph) {
            this.graph = graph;
            this.nrSccs = nrSccs;
            this.lessNodes = lessNodes;
            this.rankedSccGraph = rankedSccGraph;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res = "The approximation of the Equational Dependency Graph "+o.cite(Citation.DA_STEIN)+
                        " contains " + this.nrSccs + " SCC" + (this.nrSccs == 1 ? "" : "s");
            if (this.lessNodes > 0) {
                res += " with " + this.lessNodes + " less node"+ (this.lessNodes == 1 ? "" : "s") + ".";
            } else {
                res += ".";
            }
            return o.export(res);
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }

            final Graph<HasTermPair, Object> g = (Graph<HasTermPair, Object>) (this.graph.getGraph());
            int count = 0;
            final List<Element> components = new ArrayList<Element>();
            for (final Cycle<HasTermPair> rankedScc : this.rankedSccGraph) {
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

        		for (final HasTermPair rule : rankedScc.getNodeObjects()) {
        		    rules.appendChild(Rule.create((TRSFunctionApplication) rule.getLeft(), rule.getRight()).toCPF(doc, xmlMetaData));
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
            final Element proof = CPFTag.AC_DEP_GRAPH_PROC.createElement(doc);
            final int n = components.size(); // add components in reverse order
            for (int i = n - 1; i >= 0; i--) {
        		proof.appendChild(components.get(i));
            }

            return CPFTag.AC_DP_PROOF.create(doc, proof);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }


        @Override
        public String toDOT() {
            return this.graph.toDOT();
        }
    }

}
