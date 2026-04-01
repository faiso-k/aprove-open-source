package aprove.input.Programs.prolog.nodes;

import java.util.*;

public class TermNode extends InternalNode {
    private int precedence;
    private List<InternalNode> arguments;

    public TermNode(String name, int precedence, int line, int pos) {
        super(name, line, pos);
        this.precedence = precedence;
        this.arguments = new ArrayList<InternalNode>();
    }

    @Override
    public List<InternalNode> getChildren() {
        return this.arguments;
    }

    @Override
    public boolean addChild(InternalNode child) {
        return this.arguments.add(child);
    }

    public int getPrecedence () {
        return this.precedence;
    }

    public int getArity () {
        return this.arguments.size();
    }

    public boolean isConstant () {
        return this.arguments.size() == 0;
    }

    public void paranthesised() {
        this.precedence = 0;
    }
}
