package aprove.verification.oldframework.Rewriting;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.Visitors.*;

public class FpEvaluator implements Evaluator {

    protected Program program;

    private FpEvaluator(Program program) {
        this.program = program;
    }

    public static FpEvaluator create(Program program) {
        return new FpEvaluator(program);
    }

    @Override
    public AlgebraTerm eval(AlgebraTerm t) {
        return FpEvalVisitor.apply(t,this.program);
    }

    @Override
    public boolean evaluable(Formula f) {
        return f.evaluable(this);
    }

    @Override
    public boolean evaluable(AlgebraTerm t) {
        // TODO Auto-generated method stub
        return false;
    }

}
