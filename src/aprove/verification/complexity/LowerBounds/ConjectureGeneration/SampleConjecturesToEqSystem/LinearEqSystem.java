package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;


public class LinearEqSystem {

    private SMTExpression<SBool> exp;

    private LinearEqSystem(SMTExpression<SBool> exp) {
        super();
        this.exp = exp;
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
    public static LinearEqSystem equivalent(SMTExpression<SInt> poly, BigInteger val) {
        List<SMTExpression<SInt>> args = new ArrayList<>(2);
        args.add(poly);
        args.add(new IntConstant(val));
        return new LinearEqSystem(new ChainableCall(ChainableSymbol.Equivalent, ImmutableCreator.create(args)));
    }

    public LinearEqSystem and(LinearEqSystem that) {
        return new LinearEqSystem(new LeftAssocCall<>(LeftAssocSymbol.And,
                this.exp,
                ImmutableCreator.create(Collections.singletonList(that.exp))));
    }

    public SMTExpression<SBool> getExpression() {
        return this.exp;
    }

    public LinearEqSystem and(SMTExpression<SBool> exp) {
        return this.and(new LinearEqSystem(exp));
    }

}
