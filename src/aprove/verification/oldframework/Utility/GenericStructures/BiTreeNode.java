package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

public class BiTreeNode<T> {
    protected T value;
    private List<BiTreeNode<T>> children = new ArrayList<>();
    private BiTreeNode<T> parent = null;

    public BiTreeNode(T value) {
        this.value = value;
    }

    public BiTreeNode<T> addChild(BiTreeNode<T> child) {
    	assert child.parent == null: "BiTree Child cannot have two parents";
    	
        children.add(child);
        child.parent = this;
        return child;
    }

    public void addChildren(List<BiTreeNode<T>> nodes) {
        for (BiTreeNode<T> node : nodes) {
            addChild(node);	
        }
    }

    public boolean isLeaf() {
        return children.isEmpty();
    }

    public T getValue() {
        return value;
    }

    public void setValue(T value) {
        this.value = value;
    }
    
    public BiTreeNode<T> getParent() {
    	return this.parent;
    }

    public List<BiTreeNode<T>> getChildren() {
		return children;
    }

    public List<BiTreeNode<T>> getLeaves() {
        List<BiTreeNode<T>> leaves = new ArrayList<>();
        collectLeaves(this, leaves);
        return leaves;
    }

    private static <T> void collectLeaves(BiTreeNode<T> node, List<BiTreeNode<T>> acc) {
        if (node.children.isEmpty()) {
            acc.add(node);
            return;
        }
        for (BiTreeNode<T> child : node.children) {
            collectLeaves(child, acc);
        }
    }

    public List<T> getLeafValues() {
        List<T> values = new ArrayList<>();
        for (BiTreeNode<T> leaf : getLeaves()) {
            values.add(leaf.value);
        }
        return values;
    }

    public List<BiTreeNode<T>> flatten() {
        List<BiTreeNode<T>> result = new ArrayList<>();
        flattenPreOrder(this, result);
        return result;
    }

    private static <T> void flattenPreOrder(BiTreeNode<T> node, List<BiTreeNode<T>> acc) {
        acc.add(node);
        for (BiTreeNode<T> child : node.children) {
            flattenPreOrder(child, acc);
        }
    }

    public List<T> flattenValues() {
        List<T> result = new ArrayList<>();
        for (BiTreeNode<T> n : flatten()) {
            result.add(n.getValue());
        }
        return result;
    }
    
    public boolean isRoot() {
    	return this.parent == null;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        toString(sb, "", true);
        return sb.toString();
    }

    private void toString(StringBuilder sb, String prefix, boolean isLast) {
        sb.append(prefix);
        sb.append(isLast ? "└─ " : "├─ ");
        sb.append(value);
        sb.append('\n');

        for (int i = 0; i < children.size(); i++) {
            children.get(i).toString(
                sb,
                prefix + (isLast ? "   " : "│  "),
                i == children.size() - 1
            );
        }
    }
}
 
