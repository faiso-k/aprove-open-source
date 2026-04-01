package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;


@SuppressWarnings("javadoc")
public class ComplexBooleanExpressionNode extends BooleanExpressionNode {

    private final BooleanExpressionNode expressionA;
    private final BooleanExpressionNode expressionB;
    private final Type type;

    public ComplexBooleanExpressionNode(
        final String text,
        final int line,
        final int position,
        final BooleanExpressionNode expA,
        final BooleanExpressionNode expB,
        final Type t)
    {
        super(text, line, position);
        this.expressionA = expA;
        this.expressionB = expB;
        this.type = t;
    }

    @Override
    public String toString() {
        final boolean simpleA = this.expressionA instanceof BinaryBooleanExpressionNode;
        final boolean simpleB = this.expressionB instanceof BinaryBooleanExpressionNode;

        return (simpleA ? "" : "(")
            + this.expressionA.toString()
            + (simpleA ? "" : ")")
            + " "
            + this.type.getSymbol()
            + " "
            + (simpleB ? "" : "(")
            + this.expressionB.toString()
            + (simpleB ? "" : ")");
    }


    public enum Type {
        AND("&&"), OR("||");

        private String symbol;

        private Type(final String s) {
            this.symbol = s;
        }

        public String getSymbol() {
            return this.symbol;
        }
    }



    @Override
    public BooleanExpressionNode negate() {
        switch (this.type) {
        case AND:
            return new ComplexBooleanExpressionNode(
                null,
                0,
                0,
                this.expressionA.negate(),
                this.expressionB.negate(),
                Type.OR);
        case OR:
            return new ComplexBooleanExpressionNode(
                null,
                0,
                0,
                this.expressionA.negate(),
                this.expressionB.negate(),
                Type.AND);
        default:
            return null;
        }
    }

    /*
        @Override
        public HashSet<String> getVariablesId() {
            final HashSet<String> result = (HashSet<String>) this.expressionA.getVariablesId().clone();
            result.addAll(this.expressionB.getVariablesId());
            return result;
        }
     */

    @Override
    public HashSet<String> getVariableNames() {
        final HashSet<String> result = (HashSet<String>) this.expressionA.getVariableNames().clone();
        result.addAll(this.expressionB.getVariableNames());
        return result;
    }

    @Override
    public
    boolean isFalse() {
        switch (this.type) {
        case AND:
            return this.expressionA.isFalse() || this.expressionB.isFalse();
        case OR:
            return this.expressionA.isFalse() && this.expressionB.isFalse();
        default:
            return false;
        }
    }

    @Override
    public boolean isTrue() {
        switch (this.type) {
        case AND:
            return this.expressionA.isTrue() && this.expressionB.isTrue();
        case OR:
            return this.expressionA.isTrue() || this.expressionB.isTrue();
        default:
            return false;
        }
    }

    //    @Override
    //    public PolyDisjunction toDisjunction() {
    //        switch (this.type) {
    //        case AND:
    //
    //            return this.expressionA
    //                .toDisjunction()
    //.mergeAll(this.expressionB.toDisjunction());
    //        case OR:
    //            return this.expressionA.toDisjunction().addAllSystems(
    //                this.expressionB.toDisjunction().getConstraintsSystems());
    //        default:
    //            return null;
    //        }
    //    }
    //
    //    @Override
    //    public boolean isNonDet() {
    //        return this.expressionA.isNonDet() || this.expressionB.isNonDet();
    //    }

    protected static BooleanExpressionNode getComplexBooleanExpression(
        final BooleanExpressionNode expA,
        final BooleanExpressionNode expB,
        final Type type)
    {
        return new ComplexBooleanExpressionNode(
            expA.getText() + type.symbol + expB.getText(),
            expA.getLine(),
            expB.getPos(),
            expA,
            expB,
            type);
    }

    @Override
    public HashSet<VariableNode> getNonDetVariables() {
        final HashSet<VariableNode> variables = this.expressionA.getNonDetVariables();
        variables.addAll(this.expressionB.getNonDetVariables());
        return variables;
    }

    @Override
    public TRSTerm toTerm() {
        switch (this.type) {
        case AND:
            return ToolBox.buildAnd(this.expressionA.toTerm(), this.expressionB.toTerm());
        case OR:
            return ToolBox.buildOr(this.expressionA.toTerm(), this.expressionB.toTerm());
        default:
            return null;
        }
    }
}
