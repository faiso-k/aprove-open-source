package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class CdtForwardInstantiationProcessor extends CdtTransformationProcessor{

    @ParamsViaArgumentObject
    public CdtForwardInstantiationProcessor(Arguments args) {
        super(args);
    }

    @Override
    protected Transformation computeTransformation(State st, Node<Cdt> node) {
        Set<Edge<BitSet,Cdt>> outEdges = st.graph.getOutEdges(node);
        if (outEdges.isEmpty()) {
            return null;
        }
        IcapCalculator icap = st.cdtGraph.getIcap();
        Cdt nodeCdt = icap.renameVarDisjoint(node.getObject());
        Set<Cdt> newCdts = new LinkedHashSet<Cdt>();
        /* Compute different instantiations */
        for (Edge<BitSet,Cdt> outEdge : outEdges) {
            Node<Cdt> outNode = outEdge.getEndNode();
            BitSet connection = outEdge.getObject();
            Cdt outNodeCdt = outNode.getObject();
            for (ListIterator<TRSFunctionApplication> it = nodeCdt.getRuleRHSArgs().listIterator(); it.hasNext();) {
                if (!connection.get(it.nextIndex())) {
                    it.next();
                    continue;
                }
                TRSTerm t = it.next();
                TRSTerm cappedLhs = icap.getCappedLhs(nodeCdt.getRuleLHS(), t, outNodeCdt);
                TRSSubstitution sigma = t.getMGU(cappedLhs);
                if (sigma == null) {
                    continue;
                }
                Set<TRSVariable> varsOfNodeCdt = nodeCdt.getRule().getVariables();
                if (sigma.restrictTo(varsOfNodeCdt).isVariableRenaming()) {
                    return null;
                }
                newCdts.add(nodeCdt.applySubstitution(sigma));
            }
        }

        Transformation result = new Transformation(true,
                GraphHistory.Technique.ForwardInstantiation, node, newCdts,
                new CdtForwardInstantiationProof(node.getObject(), newCdts));
        return result;
    }

    static class CdtForwardInstantiationProof extends CpxProof {

        private final Cdt oldCdt;
        private final Set<Cdt> newCdts;

        public CdtForwardInstantiationProof(Cdt old, Set<Cdt> instantiations) {
            this.oldCdt = old;
            this.newCdts = instantiations;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("Use forward instantiation to replace "));
            sb.append(o.export(this.oldCdt));
            sb.append(o.escape(" by "));
            sb.append(o.set(this.newCdts, Export_Util.RULES));
            return sb.toString();
        }

    }

}
