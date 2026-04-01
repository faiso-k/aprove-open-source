package aprove.verification.dpframework.IDPProblem.Processors;


import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.Node;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

@NoParams
public class IDependencyGraphProcessor extends IDPProcessor {

    @Override
    public boolean isIDPApplicable(IDPProblem idp) {
        return idp.getIdpGraph().isSCC() != YNM.YES;
    }


    @Override
    protected Result processIDPProblem(IDPProblem idp, Abortion aborter)
            throws AbortionException {
        IIDependencyGraph graph = idp.getIdpGraph();

        Collection<IIDependencyGraph> subSccs = graph.splitIntoSCCs(this);
        if (subSccs.size() == 1  && subSccs.iterator().next().getNodes().equals(graph.getNodes())) {
            return ResultFactory.unsuccessful();
        }
        Set<IDPProblem> newProblems = new LinkedHashSet<IDPProblem>();
        ArrayList<BasicObligation> resultObls = new ArrayList<BasicObligation>(subSccs.size());
        int size = 0;
        for (IIDependencyGraph subScc : subSccs) {
            IDPProblem newProblem = idp.change(subScc, null, null, null, this);
            newProblems.add(newProblem);
            resultObls.add(newProblem);
            size += newProblem.getP().size();
        }

        int lessNodes = idp.getP().size() - size;
        int nrSccs = newProblems.size();
        Result result = ResultFactory.provedAnd(newProblems, YNMImplication.EQUIVALENT, new IDependencyGraphProof(graph, subSccs, nrSccs, lessNodes, idp, resultObls));
        return result;
    }

    private static class IDependencyGraphProof extends Proof.DefaultProof implements DOT_Able {

        private final IIDependencyGraph graph;
        private final int nrSccs;
        private final int lessNodes;
        private final Collection<IIDependencyGraph> subSccs;
        private final BasicObligation origObl;
        private final List<BasicObligation> resultObls;

        private IDependencyGraphProof(IIDependencyGraph graph, Collection<IIDependencyGraph> subSccs, int nrSccs, int lessNodes, BasicObligation origObl, List<BasicObligation> resultObls) {
            this.graph = graph;
            this.nrSccs = nrSccs;
            this.lessNodes = lessNodes;
            this.subSccs = subSccs;
            this.origObl = origObl;
            this.resultObls = resultObls;
        }

        private static final Citation[] citations = new Citation[]{Citation.LPAR04, Citation.FROCOS05, Citation.EDGSTAR};

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res = "The approximation of the Dependency Graph "+o.cite(IDependencyGraphProof.citations)+" contains " + this.nrSccs + " SCC" + (this.nrSccs == 1 ? "" : "s");
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

        @Override
        public Element toDOM(Document doc, XMLMetaData xmlMetaData) {
            super.toDOM(doc, xmlMetaData);
            Element e = XMLTag.QDP_DEPENDENCY_GRAPH_PROOF.createElement(doc);
            for (IIDependencyGraph scc : this.subSccs) {
                Element sc = XMLTag.QDP_SCC.createElement(doc);
                for (Node node : scc.getNodes()) {
                    Element id = XMLTag.createIdentifier(doc, node.id + "");
                    sc.appendChild(id);
                }
                e.appendChild(sc);
            }
            return e;
        }

    }

}