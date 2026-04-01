package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;


@SuppressWarnings("javadoc")
public class ConstantBooleanExpressionNode extends BooleanExpressionNode {

    private final boolean value;

    /**
     * @param v - value
     */
    public ConstantBooleanExpressionNode(final String text, final int line, final int position, final boolean v) {
        super(text, line, position);
        this.value = v;
    }

    @Override
    public String toString() {
        return String.valueOf(this.value);
    }



    @Override
    public BooleanExpressionNode negate() {
        return new ConstantBooleanExpressionNode("", 0, 0, !this.value);
    }

    final public static BooleanExpressionNode True = new ConstantBooleanExpressionNode("", 0, 0, true);
    final public static BooleanExpressionNode False = new ConstantBooleanExpressionNode("", 0, 0, false);

    /*@Override
    public HashSet<String> getVariablesId() {
        return new HashSet<>();
    }*/

    @Override
    public HashSet<String> getVariableNames() {
        return new HashSet<>();
    }

    @Override
    public boolean isFalse() {
        return !this.value;
    }

    @Override
    public boolean isTrue() {
        return this.value;
    }

    //    @Override
    //    public PolyDisjunction toDisjunction() {
    //        return PolyDisjunction.create(this.value);
    //    }
    //
    //    @Override
    //    public boolean isNonDet() {
    //        return false;
    //    }

    @Override
    public HashSet<VariableNode> getNonDetVariables() {
        return new HashSet<>();
    }

    @Override
    public TRSTerm toTerm() {
        return ToolBox.buildBool(this.value);
    }
}
