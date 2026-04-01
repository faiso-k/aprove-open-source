package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;


public class SubstitutingExpressionVisitor implements ExpressionVisitor<SMTExpression<? extends Sort>>{

    private Map<? extends Symbol0<?>, ? extends SMTExpression<?>> replacementMap;

    public SubstitutingExpressionVisitor(Map<? extends Symbol0<?>, ? extends SMTExpression<?>> replacementMap) {
        this.replacementMap = replacementMap;
    }

    public SubstitutingExpressionVisitor(Symbol0<?> oldVar, Symbol0<?> newVar) {
        this(Collections.singletonMap(oldVar, newVar));
    }

    @Override
    public <RV extends Sort, A0 extends Sort> SMTExpression<?> visit(Call1<RV, A0> call1) {
        return new Call1<RV, A0>(call1.getSym(), (SMTExpression<A0>) call1.getA0().accept(this));
    }

    @Override
    public
        <RV extends Sort, A0 extends Sort, A1 extends Sort>
        SMTExpression<?>
        visit(Call2<RV, A0, A1> call2)
    {
        return new Call2<RV, A0, A1>(
            call2.getSym(),
            (SMTExpression<A0>) call2.getA0().accept(this),
            (SMTExpression<A1>) call2.getA1().accept(this));
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> SMTExpression<?> visit(
        Call3<RV, A0, A1, A2> call3)
    {
        return new Call3<RV, A0, A1, A2>(
            (Symbol3<RV, A0, A1, A2>) call3.getSym(),
            (SMTExpression<A0>) call3.getA0().accept(this),
            (SMTExpression<A1>) call3.getA1().accept(this),
            (SMTExpression<A2>) call3.getA2().accept(this));
    }

    @Override
    public <A0 extends Sort> SMTExpression<?> visit(ChainableCall<A0> chainableCall) {
        return new ChainableCall<A0>(chainableCall.getSym(), this.visit(chainableCall.getArgs()));
    }

    @Override
    public <S extends Sort> SMTExpression<?> visit(Exists<S> exists) {
        SMTExpression<? extends Sort> newBody = exists.getBody().accept(this);
        return new Exists<Sort>(exists.getType(), this.visit(exists.getVars()), newBody);
    }

    @Override
    public <S extends Sort> SMTExpression<?> visit(Forall<S> forall) {
        SMTExpression<? extends Sort> newBody = forall.getBody().accept(this);
        return new Forall<Sort>(forall.getType(), this.visit(forall.getVars()), newBody);
    }

    @Override
    public SMTExpression<?> visit(IntConstant intConstant) {
        return intConstant;
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> SMTExpression<?> visit(LeftAssocCall<A0, A1> leftAssocCall) {
        SMTExpression<A0> first = (SMTExpression<A0>) leftAssocCall.getFirst().accept(this);
        return new LeftAssocCall<A0, A1>(leftAssocCall.getSym(), first, this.visit(leftAssocCall.getArgs()));
    }

    @Override
    public <S extends Sort> SMTExpression<?> visit(Let<S> let) {
        throw new NotYetImplementedException();
    }

    @Override
    public <A0 extends Sort> SMTExpression<?> visit(PairwiseCall<A0> pairwiseCall) {
        return new PairwiseCall<A0>(pairwiseCall.getSym(), this.visit(pairwiseCall.getArgs()));
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> SMTExpression<?> visit(RightAssocCall<A0, A1> rightAssocCall) {
        SMTExpression<A1> last = (SMTExpression<A1>) rightAssocCall.getLast().accept(this);
        return new RightAssocCall<A0, A1>(rightAssocCall.getSym(), this.visit(rightAssocCall.getArgs()), last);
    }

    @Override
    public <S extends Sort> SMTExpression<?> visit(Symbol0<S> symbol0) {
        if (this.replacementMap.containsKey(symbol0)) {
            return this.replacementMap.get(symbol0);
        } else {
            return symbol0;
        }
    }

    private <T extends SMTExpression<?>> ImmutableList<T> visit(List<? extends T> l) {
        List<T> newL = new LinkedList<>();
        for (T e : l) {
            newL.add((T) e.accept(this));
        }
        return ImmutableCreator.create(newL);
    }
}
