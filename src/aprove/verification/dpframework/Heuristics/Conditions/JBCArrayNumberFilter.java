package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;

public class JBCArrayNumberFilter extends AbstractITRSCondition {
    public static class Arguments {
        public int limitRatio = 100;
    }

    private final int limitRatio;

    @ParamsViaArgumentObject
    public JBCArrayNumberFilter(final Arguments arguments) {
        this.limitRatio = arguments.limitRatio;
    }

    @Override
    public boolean checkITRS(final ITRSProblem itrs, final Abortion aborter) {
        int arrayNumber = 0;
        for (final GeneralizedRule rule : itrs.getR()) {
            arrayNumber += this.numberOfArrays(rule.getLeft());
        }
        final int arrayRatio = (int) ((float) arrayNumber / (float) itrs.getR().size() * 100);
        if (Globals.DEBUG_MARC) {
            System.err.println("Array ratio: " + arrayRatio);
        }

        return (arrayRatio >= this.limitRatio);
    }

    private int numberOfArrays(final TRSFunctionApplication term) {
        int count = 0;

        for (final TRSTerm arg : term.getArguments()) {
            if (arg instanceof TRSVariable) {
                continue;
            }
            final TRSFunctionApplication fa = (TRSFunctionApplication) arg;
            if (!fa.getRootSymbol().getName().equals(InstanceTransformer.JAVA_LANG_OBJECT_NAME.getName())
                || !(fa.getRootSymbol().getArity() == InstanceTransformer.JAVA_LANG_OBJECT_NAME.getArity())) {
                continue;
            }
            if (fa.getRootSymbol().getArity() != 1 || fa.getArgument(0) instanceof TRSVariable) {
                continue;
            }
            final TRSFunctionApplication innerFa = (TRSFunctionApplication) fa.getArgument(0);
            if (innerFa.getRootSymbol().getName().equals(ArrayTransformer.ARRAY_CONSTR.getName())
                && innerFa.getRootSymbol().getArity() == ArrayTransformer.ARRAY_CONSTR.getArity()) {
                count += 1;
            }
        }

        return count;
    }

    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }
}
