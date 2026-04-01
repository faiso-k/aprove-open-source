package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import immutables.*;

public final class Success extends ExecutableStrategy implements Immutable {

    public static final Success EMPTY;

    static {
        EMPTY = new Success(Collections.<BasicObligationNode>emptyList());
    }

    private final ImmutableList<BasicObligationNode> positions;

    private Success(List<BasicObligationNode> positions) {
        super(null);
        this.positions = ImmutableCreator.create(positions);
    }

    public Success(Collection<? extends BasicObligationNode> positions) {
        this(new ArrayList<BasicObligationNode>(positions));
    }

    public Success(BasicObligationNode position) {
        this(Collections.singletonList(position));
    }

    @Override
    public boolean isNormal() {
        return true;
    }

    public ImmutableList<BasicObligationNode> getPositions() {
        return ImmutableCreator.create(this.positions);
    }

    @Override
    ExecutableStrategy exec() {
        throw new RuntimeException("You should not execute Success");
    }

    @Override
    void stop(String reason) {
    }

    @Override
    public String toString() {
        String res = "Success(";
        boolean first = true;
        for (BasicObligationNode oblNode : this.positions) {
            if (first) {
                first = false;
            } else {
                res += ", ";
            }
            res += oblNode.getBasicObligation().getId();
        }
        return res+")";
    }



}
