package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class ProgramNode extends InternalNode {
    private List<InternalNode> sentences;

    public ProgramNode () {
        super("Program", -1, -1);
        this.sentences = new ArrayList<InternalNode>();
    }

    @Override
    public List<InternalNode> getChildren() {
        return this.sentences;
    }

    @Override
    public boolean addChild(InternalNode child) {
        if (child instanceof SentenceNode) {
            return this.sentences.add(child);
        }
        return false;
    }
}
