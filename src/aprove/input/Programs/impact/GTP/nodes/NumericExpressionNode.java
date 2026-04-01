package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.input.Programs.impact.GTP.nodes.BinrayNumericExpressionNode.*;

@SuppressWarnings("javadoc")
public abstract class NumericExpressionNode extends BooleanExpressionNode {

    public NumericExpressionNode(final String text, final int line, final int position) {
        super(text, line, position);
    }

    public abstract HashSet<String> getVariablesId();


    //  public abstract SimplePolyFraction getPolyFraction();

    // public abstract SimplePolynomial getDenumeratorPolynomial();

    // public abstract SimplePolynomial getValue(HashMap<String, BigInteger> valuesMap);

    // @Override
    // public abstract boolean isNonDet();

    // public NumericExpressionNode negate(int line, int pos) , //

    public BooleanExpressionNode toBooleanExpressionNode() {
        final NumericExpressionNode expA = this;
        final NumericExpressionNode expB = new ConstantNumericExpressionNode("0", 0, 0, 0);
        final BinaryBooleanExpressionNode.Type type = BinaryBooleanExpressionNode.Type.GREATER;

        final BooleanExpressionNode boolA =
            new BinaryBooleanExpressionNode(expA.getText() + type.getSymbol() + expB.getText(), 0, 0, expA, expB, type);
        final BooleanExpressionNode boolB =
            new BinaryBooleanExpressionNode(expB.getText() + type.getSymbol() + expA.getText(), 0, 0, expB, expA, type);
        final ComplexBooleanExpressionNode.Type typeII = ComplexBooleanExpressionNode.Type.OR;

        return new ComplexBooleanExpressionNode(
            boolA.getText() + typeII.getSymbol() + boolB.getText(),
            0,
            0,
            boolA,
            boolB,
            typeII);
    }

    @Override
    public BooleanExpressionNode negate() {
        return this.toBooleanExpressionNode().negate();
    }

    @Override
    public boolean isFalse() {
        return this.toBooleanExpressionNode().isFalse();
    }

    @Override
    public boolean isTrue() {
        return this.toBooleanExpressionNode().isTrue();
    }

    //    @Override
    //    public PolyDisjunction toDisjunction() {
    //        return this.toBooleanExpressionNode().toDisjunction();
    //    }

    public NumericExpressionNode times (final NumericExpressionNode exp)  {
        return BinrayNumericExpressionNode.getBinaryExpression(this, exp, Type.MUL);
    }

    public NumericExpressionNode add(final NumericExpressionNode exp) {
        return BinrayNumericExpressionNode.getBinaryExpression(this, exp, Type.ADD);
    }

    public NumericExpressionNode sub(final NumericExpressionNode exp) {
        return BinrayNumericExpressionNode.getBinaryExpression(this, exp, Type.SUB);
    }
}
