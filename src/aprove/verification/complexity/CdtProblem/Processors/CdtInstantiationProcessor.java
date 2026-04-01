package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class CdtInstantiationProcessor extends CdtTransformationProcessor{

    @ParamsViaArgumentObject
    public CdtInstantiationProcessor(Arguments args) {
        super(args);
    }

    @Override
    protected Transformation computeTransformation(State st, Node<Cdt> node) {
        Set<Edge<BitSet,Cdt>> inEdges = st.graph.getInEdges(node);
        if (inEdges.isEmpty()) {
            return null;
        }
        IcapCalculator icap = st.cdtGraph.getIcap();
        Cdt nodeCdt = icap.renameVarDisjoint(node.getObject());
        TRSFunctionApplication nodeLhs = nodeCdt.getRuleLHS();
        Set<Cdt> newCdts = new LinkedHashSet<Cdt>();
        /* Compute different instantiations */
        for (Edge<BitSet,Cdt> inEdge : inEdges) {
            Node<Cdt> inNode = inEdge.getStartNode();
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
        if (CdtInstantiationProcessor.newStartNodeNecessary(nodeCdt, newCdts, st.cdtProblem.getDefinedRSymbols())) {
            Rule newRule = this.renameLhsRoot(st, nodeCdt.getRule());
            newCdts.add(Cdt.create(newRule));
        }

        Transformation result = new Transformation(true,
                GraphHistory.Technique.Instantiation, node, newCdts,
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

    /**
     * A new start node is necessary, if any of the replacement nodes contains
     * now a defined symbol on the lhs (and did not before).
     */
    public static boolean newStartNodeNecessary(Cdt oldCdt, Set<Cdt> newCdts, Set<FunctionSymbol> definedRSymbols) {
        if (!Collections.disjoint(oldCdt.getRuleLHS().getFunctionSymbols(), definedRSymbols)) {
            return false;
        }
        for (Cdt newCdt : newCdts) {
            Set<FunctionSymbol> leftSyms = newCdt.getRuleLHS().getFunctionSymbols();
            if (!Collections.disjoint(leftSyms, definedRSymbols)) {
                return true;
            }
        }
        return false;
    }

    static class CdtInstantiationProof extends CpxProof {

        private final Cdt oldCdt;
        private final Set<Cdt> newCdts;

        public CdtInstantiationProof(Cdt old, Set<Cdt> instantiations) {
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
