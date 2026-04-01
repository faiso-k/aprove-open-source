package aprove.verification.idpframework.Processors.Filters;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class VariablePartitionGraph {

    private final SimpleGraph<VariablePartitionPos, Unused> graph;
    private final Map<VariablePartitionPos, Node<VariablePartitionPos>> varToNode;
    private final Set<Node<VariablePartitionPos>> rootNodes;

    private final Set<VariablePartitionPos> checkedPositions;

    public VariablePartitionGraph() {
        this.graph = new SimpleGraph<VariablePartitionPos, Unused>();
        this.varToNode = new LinkedHashMap<VariablePartitionPos, Node<VariablePartitionPos>>();
        this.rootNodes = new LinkedHashSet<Node<VariablePartitionPos>>();
        this.checkedPositions = new LinkedHashSet<VariablePartitionPos>();
    }

    public boolean addEdgeVariable(final VariablePartitionPos from, final VariablePartitionPos to) {
        final Node<VariablePartitionPos> fromNode = this.getNode(from);
        final Node<VariablePartitionPos> toNode = this.getNode(to);

        this.rootNodes.remove(toNode);

        if (this.graph.addEdge(fromNode, toNode)) {
//            System.err.println("EDGE " + fromNode + " -> " + toNode);
            return true;
        } else {
            return false;
        }
    }

    public void addCheckedPositions(final Collection<? extends VariablePartitionPos> checked) {
//        System.err.println("CHECKED " + checked);
        this.checkedPositions.addAll(checked);
    }

    public void addCheckedPosition(final VariablePartitionPos checked) {
//        System.err.println("CHECKED " + checked);
        this.checkedPositions.add(checked);
    }

    public void addCheckedVars(final Set<IVariable<?>> variables) {
        for (final IVariable<?> var : variables) {
            this.checkedPositions.add(new VariablePartitionPos(var));
        }
    }

    public Set<ImmutableSet<VariablePartitionPos>> getPartitions() {
        final Set<ImmutableSet<VariablePartitionPos>> res = new LinkedHashSet<ImmutableSet<VariablePartitionPos>>();

        final Set<Node<VariablePartitionPos>> remainingNodes = new LinkedHashSet<Node<VariablePartitionPos>>(this.graph.getNodes());
        // guess this is not needed, but unsure
//        for (final Node<VariablePartitionPos> rootNode : rootNodes) {
//            final Set<Node<VariablePartitionPos>> reachableNodes = new LinkedHashSet<Node<VariablePartitionPos>>();
//            collectReachableNodes(rootNode, reachableNodes);
//
//            remainingNodes.removeAll(reachableNodes);
//
//            final Set<VariablePartitionPos> varPatition = new LinkedHashSet<VariablePartitionPos>();
//            for (final Node<VariablePartitionPos> node : reachableNodes) {
//                varPatition.add(node.getObject());
//            }
//            res.add(ImmutableCreator.create(varPatition));
//        }

        final LinkedHashSet<Cycle<VariablePartitionPos>> sccs = this.graph.getSCCs(new EdgeFilter<Unused, VariablePartitionPos>() {

            @Override
            public boolean selectEdge(final Node<VariablePartitionPos> source,
                final Node<VariablePartitionPos> dest,
                final Unused label) {
                return remainingNodes.contains(source) && remainingNodes.contains(dest);
            }
        });

        for (final Cycle<VariablePartitionPos> cycle : sccs) {
            final Set<Node<VariablePartitionPos>> sccNodes = new LinkedHashSet<Node<VariablePartitionPos>>(cycle);

            boolean isChecked = false;
            for (final Node<VariablePartitionPos> sccNode : sccNodes) {
                if (this.checkedPositions.contains(sccNode.getObject())) {
                    isChecked = true;
                    break;
                }
            }

            if (isChecked) {
                final Set<Node<VariablePartitionPos>> reachableNodes = new LinkedHashSet<Node<VariablePartitionPos>>();

                this.collectReachableNodes(sccNodes.iterator().next(), reachableNodes);

                final Set<VariablePartitionPos> varPatition = new LinkedHashSet<VariablePartitionPos>();
                for (final Node<VariablePartitionPos> node : reachableNodes) {
                    varPatition.add(node.getObject());
                }
                res.add(ImmutableCreator.create(varPatition));
            }
        }

        return res;
    }

    private void collectReachableNodes(final Node<VariablePartitionPos> fromNode, final Set<Node<VariablePartitionPos>> reachableNodes) {
        if (reachableNodes.add(fromNode)) {
            for (final Node<VariablePartitionPos> succNode : this.graph.getOut(fromNode)) {
                this.collectReachableNodes(succNode, reachableNodes);
            }
        }
    }

    private Node<VariablePartitionPos> getNode(final VariablePartitionPos var) {
        Node<VariablePartitionPos> node = this.varToNode.get(var);

        if (node == null) {
            node = new Node<VariablePartitionPos>(var);
            this.graph.addNode(node);
            this.varToNode.put(var, node);
            this.rootNodes.add(node);
        }

        return node;
    }

}
