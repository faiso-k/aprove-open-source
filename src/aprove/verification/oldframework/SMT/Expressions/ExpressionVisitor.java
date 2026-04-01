package aprove.verification.oldframework.SMT.Expressions;

import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public interface ExpressionVisitor<T> {

    <RV extends Sort, A0 extends Sort> T visit(Call1<RV, A0> call1);

    <RV extends Sort, A0 extends Sort, A1 extends Sort> T visit(Call2<RV, A0, A1> call2);

    <RV extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> T visit(Call3<RV, A0, A1, A2> call3);

    <A0 extends Sort> T visit(ChainableCall<A0> chainableCall);

    <S extends Sort> T visit(Exists<S> exists);

    <S extends Sort> T visit(Forall<S> forall);

    T visit(IntConstant intConstant);

    <A0 extends Sort, A1 extends Sort> T visit(LeftAssocCall<A0, A1> leftAssocCall);

    <S extends Sort> T visit(Let<S> let);

    <A0 extends Sort> T visit(PairwiseCall<A0> pairwiseCall);

    <A0 extends Sort, A1 extends Sort> T visit(RightAssocCall<A0, A1> rightAssocCall);

    <S extends Sort> T visit(Symbol0<S> symbol0);
}
