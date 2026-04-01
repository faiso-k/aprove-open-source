package aprove.input.Programs.impact.GTP.nodes;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;

@SuppressWarnings("javadoc")
public class ConstantNumericExpressionNode extends SimpleNumericExpressionNode {

    private final long value;

    /**
     * @param v - value
     */
    public ConstantNumericExpressionNode(final String text, final int line, final int position, final long v) {
        super(text, line, position);
        this.value = v;
    }

    public long getValue() {
        return this.value;
    }

    @Override
    public String toString() {
        return String.valueOf(this.value);
    }

    //
    //    @Override
    //    public SimplePolynomial getNumeratorPolynomial()
    //    {
    //        return SimplePolynomial.create(this.value);
    //    }
    //
    //    @Override
    //    public SimplePolynomial getDenumeratorPolynomial()
    //    {
    //        return SimplePolynomial.create(1);
    //    }

    @Override
    public HashSet<String> getVariablesId() {
        return new HashSet<>();
    }

    @Override
    public HashSet<String> getVariableNames() {
        return new HashSet<>();
    }

    //    @Override
    //    public boolean isNonDet() {
    //        return false;
    //    }

    @Override
    public BooleanExpressionNode negate() {
        return new ConstantBooleanExpressionNode(this.getText(), this.getPos(), this.getLine(), this.isFalse());
    }

    @Override
    public boolean isFalse() {
        return this.value == 0;
    }

    @Override
    public boolean isTrue() {
        return !this.isFalse();
    }

    //    @Override
    //    public PolyDisjunction toDisjunction() {
    //        return PolyDisjunction.create(this.isTrue());
    //    }

    public static NumericExpressionNode ZERO = new ConstantNumericExpressionNode("0", 0, 0, 0);
    public static NumericExpressionNode ONE = new ConstantNumericExpressionNode("1", 0, 0, 1);

    @Override
    public HashSet<VariableNode> getNonDetVariables() {
        return new HashSet<>();
    }

    //    @Override
    //    public SimplePolyFraction getPolyFraction() {
    //        return SimplePolyFraction.create(BigInteger.valueOf(this.value));
    //    }

    @Override
    public TRSTerm toTerm() {
        return ToolBox.buildInt(BigInteger.valueOf(this.value));
    }

    //    @Override
    //    public NumericExpressionNode negate(final int line, final int pos) {
    //        // TODO Auto-generated method stub
    //        return new ConstantNumericExpressionNode("-" + this.getText(), line, pos, -this.value);
    //    }


}
