package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class InfNode extends InternalNode {

    public InfNode(int line, int pos) {
        super("inf", line, pos);
    }

    public InfNode(String name, int line, int pos) {
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
