package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class AcdtInstantiationProcessor extends AcdtTransformationProcessor{

    @Override
    protected Transformation computeTransformation(State st, Node<Acdt> node) {
        Set<Edge<BitSet,Acdt>> inEdges = st.graph.getInEdges(node);
        if (inEdges.isEmpty()) {
            return null;
        }
        IcapCalculator icap = st.cdtGraph.getIcap();
        Acdt nodeCdt = icap.renameVarDisjoint(node.getObject());
        TRSFunctionApplication nodeLhs = nodeCdt.getRuleLHS();
        Set<Acdt> newCdts = new LinkedHashSet<Acdt>();
        /* Compute different instantiations */
        for (Edge<BitSet,Acdt> inEdge : inEdges) {
            Node<Acdt> inNode = inEdge.getStartNode();
            BitSet connection = inEdge.getObject();
            List<TRSTerm> cappedRhss =
                icap.getCappedRhs(inNode.getObject());
            for (ListIterator<TRSTerm> it = cappedRhss.listIterator(); it.hasNext();) {
                if (!connection.get(it.nextIndex())) {
                    it.next();
                    continue;
                }
                TRSTerm t = it.next();
                TRSSubstitution sigma = t.getMGU(nodeLhs);
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

        /* Add new start node */
        if (AcdtGraphRemoveDanglingNodesProcessor.leadingNodeNecessary(node, st.cdtProblem.getDefinedRSymbols())) {
            Rule newRule = this.renameLhsRoot(st, nodeCdt.getRule());
            Rule newBaseRule = this.renameLhsRoot(st, nodeCdt.getBaseRule());
            newCdts.add(Acdt.create(newRule, newBaseRule, nodeCdt.getTupleDefPos()));
        }

        Transformation result = new Transformation(
                Collections.singletonMap(node, newCdts),
                new CdtInstantiationProof(node.getObject(), newCdts));
        return result;
    }

    private Rule renameLhsRoot(State st, Rule r) {
        FunctionSymbol oldRootSym = r.getRootSymbol();
        String newName = st.fng.getFreshName(oldRootSym.getName(), true);
        FunctionSymbol newRootSym = FunctionSymbol.create(newName, oldRootSym.getArity());
        TRSFunctionApplication newLhs =
            TRSTerm.createFunctionApplication(newRootSym, r.getLeft().getArguments());
        return Rule.create(newLhs, r.getRight());
    }

    static class CdtInstantiationProof extends DefaultProof {

        private final Acdt oldCdt;
        private final Set<Acdt> newCdts;

        public CdtInstantiationProof(Acdt old, Set<Acdt> instantiations) {
            this.oldCdt = old;
            this.newCdts = instantiations;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("Use instantiation to replace "));
            sb.append(o.export(this.oldCdt));
            sb.append(o.escape(" by "));
            sb.append(o.set(this.newCdts, Export_Util.RULES));
            return sb.toString();
        }

    }
}
