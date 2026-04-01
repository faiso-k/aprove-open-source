package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;

@SuppressWarnings("javadoc")
public class BinrayNumericExpressionNode extends NumericExpressionNode {
    private final Type type;
    private final NumericExpressionNode expressionA;
    private final NumericExpressionNode expressionB;

    public BinrayNumericExpressionNode(
        final String text,
        final int line,
        final int position,
        final NumericExpressionNode expA,
        final NumericExpressionNode expB,
        final Type t)
    {
        super(text, line, position);
        this.expressionA = expA;
        this.expressionB = expB;
        this.type = t;
    }

    @Override
    public String toString() {
        final boolean simpleA =
            this.expressionA instanceof SimpleNumericExpressionNode
            || this.expressionA instanceof NegatedNumericExpressionNode;
        final boolean simpleB = this.expressionB instanceof SimpleNumericExpressionNode;

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
        ADD("+"), SUB("-"), MUL("*"), DIV("/");

        private String symbol;

        private Type(final String s) {
            this.symbol = s;
        }

        public String getSymbol() {
            return this.symbol;
        }
    }

    @Override
    public HashSet<String> getVariablesId() {
        final HashSet<String> variablesId = this.expressionA.getVariablesId();
        variablesId.addAll(this.expressionB.getVariablesId());
        return variablesId;
    }

    //    @Override
    //    public SimplePolynomial getNumeratorPolynomial()
    //    {
    //        final SimplePolynomial numeratorA = this.expressionA.getNumeratorPolynomial();
    //        final SimplePolynomial numeratorB = this.expressionB.getNumeratorPolynomial();
    //
    //        final SimplePolynomial denumeratorA = this.expressionA.getDenumeratorPolynomial();
    //        final SimplePolynomial denumeratorB = this.expressionB.getDenumeratorPolynomial();
    //
    //        switch (this.type) {
    //        case ADD:
    //            return numeratorA.times(denumeratorB).plus(numeratorB.times(denumeratorA));
    //        case SUB:
    //            return numeratorA.times(denumeratorB).minus(numeratorB.times(denumeratorA));
    //        case MUL:
    //            return numeratorA.times(numeratorB);
    //        case DIV:
    //            return numeratorA.times(denumeratorB);
    //        default:
    //            return null;
    //        }
    //    }
    //
    //    @Override
    //    public SimplePolynomial getDenumeratorPolynomial()
    //    {
    //        final SimplePolynomial numeratorB = this.expressionB.getNumeratorPolynomial();
    //
    //        final SimplePolynomial denumeratorA = this.expressionA.getDenumeratorPolynomial();
    //        final SimplePolynomial denumeratorB = this.expressionB.getDenumeratorPolynomial();
    //
    //        switch (this.type) {
    //        case ADD:
    //        case SUB:
    //        case MUL:
    //            return denumeratorA.times(denumeratorB);
    //        case DIV:
    //            return denumeratorA.times(numeratorB);
    //        default:
    //            return null;
    //        }
    //
    //    }

    @Override
    public HashSet<String> getVariableNames() {
        final HashSet<String> variablesId = this.expressionA.getVariableNames();
        variablesId.addAll(this.expressionB.getVariableNames());

        return variablesId;

    }

    //    @Override
    //    public boolean isNonDet() {
    //        switch (this.type) {
    //        case MUL:
    //            return (this.expressionA.isNonDet() && !this.expressionB.getPolyFraction().isZero() || this.expressionB
    //                .isNonDet() && !this.expressionA.getPolyFraction().isZero());
    //        case ADD:
    //        case SUB:
    //        case DIV:
    //            return this.expressionA.isNonDet() || this.expressionB.isNonDet();
    //        default:
    //            return false;
    //        }
    //    }

    //    @Override
    //    public NumericExpressionNode negate(final int line, final int pos) {
    //        final NumericExpressionNode expA = this.expressionA.negate(line, pos);
    //
    //        switch (this.type) {
    //        case ADD:
    //            return new BinrayNumericExpressionNode("-" + this.getText(), line, pos, expA, this.expressionB, Type.SUB);
    //        case SUB:
    //            return new BinrayNumericExpressionNode("-" + this.getText(), line, pos, expA, this.expressionB, Type.ADD);
    //        case MUL:
    //            return new BinrayNumericExpressionNode("-" + this.getText(), line, pos, expA, this.expressionB, Type.MUL);
    //        case DIV:
    //            return new BinrayNumericExpressionNode("-" + this.getText(), line, pos, expA, this.expressionB, Type.DIV);
    //        default:
    //            return null;
    //        }
    //    }

    protected static NumericExpressionNode getBinaryExpression(
        final NumericExpressionNode expA,
        final NumericExpressionNode expB,
        final Type type)
    {
        return new BinrayNumericExpressionNode(
            expA.getText() + type.symbol + expB.getText(),
            expA.getLine(),
            expA.getPos(),
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

    //    @Override
    //    public SimplePolyFraction getPolyFraction() {
    //        switch (this.type) {
    //        case MUL:
    //            return this.expressionA.getPolyFraction().times(this.expressionB.getPolyFraction());
    //        case ADD:
    //            return this.expressionA.getPolyFraction().plus(this.expressionB.getPolyFraction());
    //        case SUB:
    //            return this.expressionA.getPolyFraction().minus(this.expressionB.getPolyFraction());
    //        case DIV:
    //            return this.expressionA.getPolyFraction().div(this.expressionB.getPolyFraction());
    //        default:
    //            return null;
    //        }
    //    }

    @Override
    public TRSTerm toTerm() {
        switch (this.type) {
        case ADD:
            return ToolBox.buildSum(Arrays.asList(this.expressionA.toTerm(), this.expressionB.toTerm()));
        case DIV:
            return ToolBox.buildDiv(this.expressionA.toTerm(), this.expressionB.toTerm());
        case MUL:
            return ToolBox.buildProduct(Arrays.asList(this.expressionA.toTerm(), this.expressionB.toTerm()));
        case SUB:
            return ToolBox.buildSum(Arrays.asList(
                this.expressionA.toTerm(),
                ToolBox.buildMinus(this.expressionB.toTerm())));
        default:
            return null;

        }
    }

}
