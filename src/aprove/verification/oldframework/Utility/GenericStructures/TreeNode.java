package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

public class TreeNode<T> {
    protected T value;
    private List<TreeNode<T>> children = new ArrayList<>();

    public TreeNode(T value) {
        this.value = value;
    }

    public void addChild(TreeNode<T> child) {
        children.add(child);
    }

    public void addChildren(List<TreeNode<T>> nodes) {
        for (TreeNode<T> node : nodes) {
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

    public List<TreeNode<T>> getChildren() {
        return children;
    }
}
 
