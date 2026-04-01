package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class AcdtForwardInstantiationProcessor extends AcdtTransformationProcessor{

    @Override
    protected Transformation computeTransformation(State st, Node<Acdt> node) {
        Set<Edge<BitSet,Acdt>> outEdges = st.graph.getOutEdges(node);
        if (outEdges.isEmpty()) {
            return null;
        }
        IcapCalculator icap = st.cdtGraph.getIcap();
        Acdt nodeCdt = icap.renameVarDisjoint(node.getObject());
        Set<Acdt> newCdts = new LinkedHashSet<Acdt>();
        /* Compute different instantiations */
        for (Edge<BitSet,Acdt> outEdge : outEdges) {
            Node<Acdt> outNode = outEdge.getEndNode();
            BitSet connection = outEdge.getObject();
            Acdt outNodeCdt = outNode.getObject();
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

        Transformation result = new Transformation(
                Collections.singletonMap(node, newCdts),
                new CdtForwardInstantiatonProof(node.getObject(), newCdts));
        return result;
    }

    static class CdtForwardInstantiatonProof extends DefaultProof {

        private final Acdt oldCdt;
        private final Set<Acdt> newCdts;

        public CdtForwardInstantiatonProof(Acdt old, Set<Acdt> instantiations) {
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
