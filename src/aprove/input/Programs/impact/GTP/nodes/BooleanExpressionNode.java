package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.input.Programs.impact.GTP.nodes.ComplexBooleanExpressionNode.*;
import aprove.verification.dpframework.BasicStructures.*;

@SuppressWarnings("javadoc")
public abstract class BooleanExpressionNode extends Node {
    public BooleanExpressionNode(final String text, final int line, final int position) {
        super(text, line, position);
    }

    //public abstract Formula toFormula(HashMap<String, String> variableSuffixMap, HashMap<String, BigInteger> valuesMap);

    public abstract BooleanExpressionNode negate();

    public abstract boolean isFalse();

    public abstract boolean isTrue();

    //  public abstract PolyDisjunction toDisjunction();

    // public abstract boolean isNonDet();

    public BooleanExpressionNode and (final BooleanExpressionNode exp) {
        return ComplexBooleanExpressionNode.getComplexBooleanExpression(this, exp, Type.AND);
    }

    public BooleanExpressionNode or(final BooleanExpressionNode exp) {
        return ComplexBooleanExpressionNode.getComplexBooleanExpression(this, exp, Type.OR);
    }

    public abstract HashSet<VariableNode> getNonDetVariables();

    public abstract TRSTerm toTerm();
}
