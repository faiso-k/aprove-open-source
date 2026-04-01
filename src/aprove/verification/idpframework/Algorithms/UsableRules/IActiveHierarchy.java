package aprove.verification.idpframework.Algorithms.UsableRules;

import java.util.*;

import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author MP
 */
public class IActiveHierarchy {

    protected final Graph<IActiveCondition, Unused> hierarchy;
    protected final Node<IActiveCondition> activeRoot;
    protected final Set<Node<IActiveCondition>> activeLeaves;
    protected final Map<IActiveCondition, Node<IActiveCondition>> conditionToNode;
    protected final Map<IActiveAtom, Node<IActiveCondition>> atomToNode;

    public IActiveHierarchy() {
        this.hierarchy = new Graph<IActiveCondition, Unused>();
        this.activeRoot = new Node<IActiveCondition>(IActiveCondition.EMPTY_CONDITION);
        this.activeLeaves = new LinkedHashSet<Node<IActiveCondition>>();
        this.conditionToNode = new LinkedHashMap<IActiveCondition, Node<IActiveCondition>>();
        this.atomToNode = new LinkedHashMap<IActiveAtom, Node<IActiveCondition>>();
        this.hierarchy.addNode(this.activeRoot);
    }

    public synchronized void addActiveCondition(final IActiveCondition activeCondition) {
        if (this.conditionToNode.containsKey(activeCondition)) {
            return;
        }

        this.addMissingAtoms(activeCondition);

        if (activeCondition.size() == 1 && activeCondition.iterator().next().y == false) {
            // just an atom
            return;
        }

        // compute parents
        final List<Node<IActiveCondition>> parents = this.getParents(activeCondition);

        // insert into hierarchy
        final Node<IActiveCondition> newNode = new Node<IActiveCondition>(activeCondition);

        this.conditionToNode.put(activeCondition, newNode);
        this.hierarchy.addNode(newNode);

        boolean isLeave = true;

        for (final Node<IActiveCondition> parent : parents) {
            for (final Node<IActiveCondition> parentSucc : new ArrayList<Node<IActiveCondition>>(
                this.hierarchy.getOut(parent))) {
                if (parentSucc.getObject().containsAll(activeCondition)) {
                    this.hierarchy.removeEdge(parent, parentSucc);
                    this.hierarchy.addEdge(newNode, parentSucc);
                    isLeave = false;
                }
            }
            this.hierarchy.addEdge(parent, newNode);
            this.activeLeaves.remove(parent);
        }

        if (isLeave) {
            this.activeLeaves.add(newNode);
        }
    }

    public synchronized Set<Node<IActiveCondition>> getNodes() {
        return new LinkedHashSet<Node<IActiveCondition>>(this.hierarchy.getNodes());
    }

    public synchronized Set<Node<IActiveCondition>> getLeaves() {
        return new LinkedHashSet<Node<IActiveCondition>>(this.activeLeaves);
    }

    public synchronized List<Node<IActiveCondition>> getParents(final Node<IActiveCondition> node) {
        return this.getParents(node.getObject());

    }

    private synchronized List<Node<IActiveCondition>> getParents(final IActiveCondition activeCondition) {
        new ArrayList<Node<IActiveCondition>>();
        return this.getDeepestChildren(this.activeRoot, activeCondition);
    }

    private synchronized void addMissingAtoms(final IActiveCondition activeCondition) {
        for (final IActiveAtom atom : activeCondition.getMap().keySet()) {
            if (!this.atomToNode.containsKey(atom)) {
                final Node<IActiveCondition> node =
                    new Node<IActiveCondition>(IActiveCondition.create(IActiveContext.create(atom)));
                this.hierarchy.addNode(node);
                this.hierarchy.addEdge(this.activeRoot, node);
                this.atomToNode.put(atom, node);
            }
        }
    }

    private synchronized List<Node<IActiveCondition>> getDeepestChildren(final Node<IActiveCondition> node,
        final IActiveCondition condition) {
        if (node.getObject().equals(condition)) {
            return Collections.emptyList();
        }

        IActiveCondition remainingCondition = condition;
        final ArrayList<Node<IActiveCondition>> result = new ArrayList<Node<IActiveCondition>>(condition.size());

        final Set<Node<IActiveCondition>> successors = this.hierarchy.getOut(node);
        for (final Node<IActiveCondition> successor : successors) {
            if (remainingCondition.containsAll(successor.getObject())) {
                final List<Node<IActiveCondition>> succChildren = this.getDeepestChildren(successor, remainingCondition);
                for (final Node<IActiveCondition> succChild : succChildren) {
                    remainingCondition = remainingCondition.subtract(succChild.getObject());
                }
                result.addAll(succChildren);
            }
        }

        if (remainingCondition.containsAll(node.getObject()) && (!node.getObject().isEmpty() || result.isEmpty())) {
            result.add(node);
        }

        return result;
    }

}
