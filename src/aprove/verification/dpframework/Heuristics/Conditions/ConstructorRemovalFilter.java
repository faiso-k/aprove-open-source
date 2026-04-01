package aprove.verification.dpframework.Heuristics.Conditions;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;

public class ConstructorRemovalFilter extends AbstractITRSCondition {
    @Override
    public boolean checkITRS(final ITRSProblem itrs, final Abortion aborter) {
        for (final GeneralizedRule rule : itrs.getR()) {
            if (this.check(rule)) {
                if (Globals.DEBUG_MARC) {
                    System.err.println("Constructor removal system");
                }
                return true;
            }
        }
        if (Globals.DEBUG_MARC) {
            System.err.println("No constructor removal system");
        }
        return false;
    }

    private boolean check(final GeneralizedRule rule) {
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        for (final TRSTerm leftArg : rule.getLeft().getArguments()) {
            if (leftArg instanceof TRSVariable) {
                continue;
            }
            final TRSFunctionApplication fa = (TRSFunctionApplication) leftArg;
            if (!fa.getRootSymbol().getName().equals(InstanceTransformer.JAVA_LANG_OBJECT_NAME.getName())
                || !(fa.getRootSymbol().getArity() == InstanceTransformer.JAVA_LANG_OBJECT_NAME.getArity())) {
                continue;
            }
            vars.addAll(fa.getVariables());
        }
        if (rule.getRight() instanceof TRSFunctionApplication) {
            for (final TRSTerm rightArg : ((TRSFunctionApplication) rule.getRight()).getArguments()) {
                if (vars.contains(rightArg)) {
                    if (rightArg.toString().startsWith("i")) {
                        continue;
                    }
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }
}
