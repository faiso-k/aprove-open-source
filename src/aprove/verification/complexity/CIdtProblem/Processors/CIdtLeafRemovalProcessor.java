package aprove.verification.complexity.CIdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


public class CIdtLeafRemovalProcessor extends CIdtProcessor<Result> {

    public CIdtLeafRemovalProcessor() {
        super("CIdtLeafRemovalProcessor");
    }

    @Override
    protected boolean isCIdtApplicable(CIdtProblem idt) {
        return true;
    }

    @Override
    protected Result processCIdtProblem(CIdtProblem idt, Abortion aborter)
            throws AbortionException {

        Set<IEdge> deletedEdges = new LinkedHashSet<IEdge>();
        Set<INode> deletedNodes = new LinkedHashSet<INode>();

        CIdtProblem newCIdt = this.deleteLeafs(idt, deletedEdges, deletedNodes);

        CIdtLeafRemovalProof proof = new CIdtLeafRemovalProof(ImmutableCreator.create(deletedNodes),
            ImmutableCreator.create(deletedEdges));

        if (idt != newCIdt) {
            ImmutableSet<IEdge> newS = CIdtProblem.cleanupS(newCIdt.getIdpGraph(), newCIdt.getS(), newCIdt.getK());
            newCIdt = newCIdt.change(newS);
            return ResultFactory.proved(newCIdt, BothBounds.create(), proof);
        } else  {
            return ResultFactory.unsuccessful();
        }
    }

    private CIdtProblem deleteLeafs(CIdtProblem idt,
        Set<IEdge> deletedEdges,
        Set<INode> deletedNodes) {

        IDependencyGraph newGraph = idt.getIdpGraph();
        ItpfFactory itpfFactory = newGraph.getItpfFactory();

        Set<EdgeType> infTypes = new LinkedHashSet<EdgeType>();
        infTypes.add(EdgeType.INF);
        infTypes.add(EdgeType.REWRITE_INF);

        Set<EdgeType> rewTypes = new LinkedHashSet<EdgeType>();
        rewTypes.add(EdgeType.REWRITE);
        rewTypes.add(EdgeType.REWRITE_INF);

        EdgeConditionMap newEdgeConditions =
            new EdgeConditionMap(newGraph.getItpfFactory(), newGraph.getFreshVarGenerator());

        Map<INode, Itpf> newNodeConditions = new LinkedHashMap<INode, Itpf>();

        Set<IEdge> newS = new LinkedHashSet<IEdge>(idt.getS());

        CIdtProblem newCIdt = idt;

        boolean success = false;
        boolean foundLeaf = true;
        while (foundLeaf) {
            foundLeaf = false;

            for (INode node : newGraph.getNodes()) {

                int infOutDegree = newGraph.getOutDegree(node, infTypes);


                if (infOutDegree == 0) {
                   boolean existsRewriteEdge = false;
                   int rewOutDegree = newGraph.getOutDegree(node, rewTypes);
                   if (rewOutDegree != 0) {
                       existsRewriteEdge = true;
                   }

                   for(Set<IEdge> preEdges : newGraph.getPredecessors(node).values()) {
                       for (IEdge preEdge : preEdges) {
                           if (preEdge.type.isRewrite()) {
                               existsRewriteEdge = true;
                           }

                           if (preEdge.type.isInf()) {
                               success = true;
                               foundLeaf = true;
                               newEdgeConditions.putFalse(preEdge);
                               deletedEdges.add(preEdge);
                               IEdge typeSubtractedEdge = preEdge.subtractType(EdgeType.INF);
                               newEdgeConditions.putOr(typeSubtractedEdge, newGraph.getCondition(preEdge));

                               this.updateS(newS, newGraph, preEdge);
                           }
                       }
                   }
                   if (!existsRewriteEdge) {
                       deletedNodes.add(node);
                       newNodeConditions.put(node, itpfFactory.createFalse());
                   }
                }
            }

            if (foundLeaf) {
                newGraph = newGraph.change(newNodeConditions, newEdgeConditions.getMap(), null, null, null, this.mark);
                newNodeConditions = new LinkedHashMap<INode, Itpf>();
            }
        }

        if (success) {
            newCIdt = idt.change(newGraph, ImmutableCreator.create(newS));
        }

        return newCIdt;
    }

    private void updateS(Set<IEdge> newS,
        IDependencyGraph newGraph,
        IEdge preEdge) {

        if (newS.remove(preEdge)) {
            for (Set<IEdge> prePreEdges : newGraph.getPredecessors(preEdge.from).values()) {
                for (IEdge prePreEdge : prePreEdges) {
                    if (prePreEdge.type.isInf()) {
                        newS.add(prePreEdge);
                    }
                }
            }
        }
    }

    @Override
    public boolean isCompatible(Mark<?> mark) {
        return false;
    }

    protected static class CIdtLeafRemovalProof extends DefaultProof {

        private ImmutableSet<INode> deletedNodes;
        private ImmutableSet<IEdge> deletedEdges;


        public CIdtLeafRemovalProof(ImmutableSet<INode> deletedNodes,
                ImmutableSet<IEdge> deletedEdges) {
            this.deletedNodes = deletedNodes;
            this.deletedEdges = deletedEdges;
        }


        @Override
        public String export(Export_Util eu, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("deleted nodes:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.deletedNodes, Export_Util.NICE_SET));

            sb.append(eu.linebreak());
            sb.append(eu.linebreak());

            sb.append("deleted edges:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.deletedEdges, Export_Util.NICE_SET));
            return sb.toString();
        }

    }

}
