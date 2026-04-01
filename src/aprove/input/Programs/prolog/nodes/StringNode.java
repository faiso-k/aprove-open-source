package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class StringNode extends InternalNode {

    public StringNode(String text, int line, int pos) {
        super(text, line, pos);
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
