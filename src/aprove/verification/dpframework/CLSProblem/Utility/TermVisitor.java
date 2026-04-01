package aprove.verification.dpframework.CLSProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public abstract class TermVisitor {

    public TRSTerm start(TRSTerm t) {
        return this.visit(t);
    }

    public TRSTerm visit(TRSTerm t) {
        TRSTerm newT;
        if (t.isVariable()) {
            newT = this.caseInVariable((TRSVariable)t);
            return newT == null ? t : newT;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication)t;
        newT = this.caseInFunctionApplication(fa);
        if (newT != null) {
            return newT;
        }
        List<? extends TRSTerm> args = fa.getArguments();
        List<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
        for (TRSTerm a : args) {
            TRSTerm newA  = this.visit(a);
            newArgs.add(newA == null ? a : newA);
        }
        TRSFunctionApplication newFa =
            TRSTerm.createFunctionApplication(fa.getRootSymbol(), ImmutableCreator.create(newArgs));
        newT = this.caseOutFunctionApplication(newFa);
        return newT == null ? newFa : newT;
    }

    public abstract TRSTerm caseInFunctionApplication(TRSFunctionApplication fa);

    public abstract TRSTerm caseInVariable(TRSVariable v);

    public abstract TRSTerm caseOutFunctionApplication(TRSFunctionApplication fa);

}
