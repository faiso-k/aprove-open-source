package aprove.verification.oldframework.SMT.Expressions;

import java.math.*;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public class IntConstant extends Constant<SInt> {
    public IntConstant(BigInteger i) {
        super(SInt.representative, i);
    }

    @Override
    public <T> T accept(ExpressionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public BigInteger getConstant() {
        return (BigInteger) super.getConstant();
    }
}
