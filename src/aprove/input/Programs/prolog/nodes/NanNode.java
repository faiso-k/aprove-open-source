package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class NanNode extends InternalNode {

    public NanNode(int line, int pos) {
        super("nan", line, pos);
    }

    public NanNode (String name, int line, int pos) {
        super(name, line, pos);
    }

    @Override
    public List<InternalNode> getChildren() {
        return null;
    }

    @Override
    public boolean addChild(InternalNode child) {
        return false;
    }

}
