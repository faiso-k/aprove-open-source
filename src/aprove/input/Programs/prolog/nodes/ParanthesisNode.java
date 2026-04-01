package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class ParanthesisNode extends InternalNode {
    private List<InternalNode> args;

    public ParanthesisNode(int line, int pos) {
        super("Paranthesis", line, pos);
        this.args = new ArrayList<InternalNode>();
    }

    @Override
    public List<InternalNode> getChildren() {
        return this.args;
    }

    @Override
    public boolean addChild(InternalNode child) {
        return this.args.add(child);
    }

}
