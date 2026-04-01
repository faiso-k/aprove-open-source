package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class PunctuationNode extends InternalNode {

    public PunctuationNode(String text, int line, int pos) {
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
