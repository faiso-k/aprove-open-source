package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class ConditionNode extends InternalNode {
    private List<InternalNode> children;

    public ConditionNode(int line, int pos) {
        super("Grammar condition", line, pos);
        this.children = new ArrayList<InternalNode>();
    }

    @Override
    public List<InternalNode> getChildren() {
        return this.children;
    }

    @Override
    public boolean addChild(InternalNode child) {
        return this.children.add(child);
    }

}
