package aprove.verification.oldframework.SMT.Expressions;

import java.math.*;
import java.security.*;

import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

/**
 * @author Hermann Walth
 * Evaluate expressions with a constant integer value,
 * which are usually either a single IntConstant c,
 * or an expression of the form (- c).
 * This is useful for evaluating models of SMT formulas
 */
public class ConstantEvalVisitor implements ExpressionVisitor<BigInteger> {

    @Override
    public <RV extends Sort, A0 extends Sort> BigInteger visit(
        Call1<RV, A0> call1
    ) {
        if (call1.getSym().equals(Symbol1.IntsNegate)) {
            return call1.getA0().accept(this).negate();
        } else {
            throw new UnsupportedOperationException("Not Implemented");
        }
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort> BigInteger visit(
        Call2<RV, A0, A1> call2
    ) {
        throw new UnsupportedOperationException("Not Implemented");
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> BigInteger visit(
        Call3<RV, A0, A1, A2> call3
    ) {
        throw new UnsupportedOperationException("Not Implemented");
    }

    @Override
    public <A0 extends Sort> BigInteger visit(ChainableCall<A0> chainableCall) {
        throw new UnsupportedOperationException("Not Implemented");
    }

    @Override
    public <S extends Sort> BigInteger visit(Exists<S> exists) {
        throw new InvalidParameterException("Can only evaluate integers");
    }

    @Override
    public <S extends Sort> BigInteger visit(Forall<S> forall) {
        throw new InvalidParameterException("Can only evaluate integers");
    }

    @Override
    public BigInteger visit(IntConstant intConstant) {
        return intConstant.getConstant();
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> BigInteger visit(
        LeftAssocCall<A0, A1> leftAssocCall
    ) {
        throw new UnsupportedOperationException("Not Implemented");
    }

    @Override
    public <S extends Sort> BigInteger visit(Let<S> let) {
        throw new InvalidParameterException("Can only evaluate integers");
    }

    @Override
    public <A0 extends Sort> BigInteger visit(PairwiseCall<A0> pairwiseCall) {
        throw new UnsupportedOperationException("Not Implemented");
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> BigInteger visit(
        RightAssocCall<A0, A1> rightAssocCall
    ) {
        throw new UnsupportedOperationException("Not Implemented");
    }

    @Override
    public <S extends Sort> BigInteger visit(Symbol0<S> symbol0) {
        throw new InvalidParameterException("Can only evaluate integers");
    }

}
