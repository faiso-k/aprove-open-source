package aprove.verification.oldframework.PropositionalLogic.Formulae;

import aprove.verification.oldframework.PropositionalLogic.*;

public class DepthFirstFormulaVisitor<T> implements FormulaVisitor<Object, T> {



    @Override
    public Object caseAnd(AndFormula<T> f) {
        this.inAnd(f);
        for (Formula<T> arg : f.args) {
            arg.apply(this);
        }
        this.outAnd(f);
        return null;
    }
    protected void outAnd(AndFormula<T> f) {}
    protected void inAnd(AndFormula<T> f) {}

    @Override
    public Object caseConstant(Constant<T> f) {
        return null;
    }

    @Override
    public Object caseIff(IffFormula<T> f) {
        this.inIff(f);
        f.left.apply(this);
        f.right.apply(this);
        this.outIff(f);
        return null;
    }
    protected void outIff(IffFormula<T> f) {}
    protected void inIff(IffFormula<T> f) {}

    @Override
    public Object caseIte(IteFormula<T> f) {
        this.inIte(f);
        f.condition.apply(this);
        f.thenFormula.apply(this);
        f.elseFormula.apply(this);
        this.outIte(f);
        return null;
    }
    protected void outIte(IteFormula<T> f) {}
    protected void inIte(IteFormula<T> f) {}

    @Override
    public Object caseNot(NotFormula<T> f) {
        this.inNot(f);
        f.arg.apply(this);
        this.outNot(f);
        return null;
    }
    protected void outNot(NotFormula<T> f) {}
    protected void inNot(NotFormula<T> f) {}

    @Override
    public Object caseOr(OrFormula<T> f) {
        this.inOr(f);
        for (Formula<T> arg : f.args) {
            arg.apply(this);
        }
        this.outOr(f);
        return null;
    }
    protected void outOr(OrFormula<T> f) {}
    protected void inOr(OrFormula<T> f) {}

    @Override
    public Object caseTheoryAtom(TheoryAtom<T> f) {
        return null;
    }

    @Override
    public Object caseVariable(Variable<T> f) {
        return null;
    }

    @Override
    public Object caseXor(XorFormula<T> f) {
        this.inXor(f);
        for (Formula<T> arg : f.args) {
            arg.apply(this);
        }
        this.outXor(f);
        return null;
    }
    protected void outXor(XorFormula<T> f) {}
    protected void inXor(XorFormula<T> f) {}


    @Override
    public Object caseAtLeast(AtLeastFormula<T> f) {
        this.inAtLeast(f);
        for (Formula<T> arg : f.args) {
            arg.apply(this);
        }
        this.outAtLeast(f);
        return null;
    }
    protected void outAtLeast(AtLeastFormula<T> f) {}
    protected void inAtLeast(AtLeastFormula<T> f) {}

    @Override
    public Object caseAtMost(AtMostFormula<T> f) {
        this.inAtMost(f);
        for (Formula<T> arg : f.args) {
            arg.apply(this);
        }
        this.outAtMost(f);
        return null;
    }
    protected void outAtMost(AtMostFormula<T> f) {}
    protected void inAtMost(AtMostFormula<T> f) {}

    @Override
    public Object caseCount(CountFormula<T> f) {
        this.inCount(f);
        for (Formula<T> arg : f.args) {
            arg.apply(this);
        }
        this.outCount(f);
        return null;
    }
    protected void outCount(CountFormula<T> f) {}
    protected void inCount(CountFormula<T> f) {}

}
