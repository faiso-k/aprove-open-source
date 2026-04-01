package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class CutNode extends InternalNode {

    public CutNode(int line, int pos) {
        super("!", line, pos);
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
