package aprove.verification.oldframework.SMT.Macros;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class IntMaxMacro extends Macro2<SInt, SInt, SInt> {

    public static final IntMaxMacro macro = new IntMaxMacro();

    private IntMaxMacro() {
        super(SInt.representative, SInt.representative, SInt.representative);
    }

    @Override
    public SMTExpression<SInt> body(SMTExpression<SInt> a0, SMTExpression<SInt> a1) {
        return Core.ite(Ints.greater(a0, a1), a0, a1);
    }

    @SafeVarargs
    public static SMTExpression<SInt> call(SMTExpression<SInt>... exps) {
        return IntMaxMacro.call(Arrays.asList(exps));
    }

    public static SMTExpression<SInt> call(List<SMTExpression<SInt>> exps) {
        SMTExpression<SInt> result = null;
        for (SMTExpression<SInt> exp : exps) {
            if (result == null) {
                result = exp;
            } else {
                result = Core.call(IntMaxMacro.macro, result, exp);
            }
        }

        if (result == null) {
            result = Ints.constant(0);
        }

        return result;
    }
}
