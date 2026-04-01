package aprove.verification.oldframework.IRSwT.Processors.TreeTraces;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Represents a tree trace, which is a TRS with the
 * following restrictions:
 * 1. Only one variable and no constant symbols are allowed.
 * 2. Rewriting steps are performed at the root position.
 * @author Matthias Hoelzel
 */
public class TreeTrace {
    private final ImmutableHashSet<IGeneralizedRule> treeTraceRules;

    final LinkedHashSet<FunctionSymbol> definedSymbols;

    public TreeTrace(final HashSet<IGeneralizedRule> inputRules) {
        this.treeTraceRules = ImmutableCreator.create(inputRules);
        this.definedSymbols = new LinkedHashSet<>();
        assert this.checkValidity() : "Invalid tree trace: " + inputRules.toString();
    }

    public ImmutableHashSet<IGeneralizedRule> getRules() {
        return this.treeTraceRules;
    }

    private boolean checkValidity() {
        // Number of variables correct?
        for (final IGeneralizedRule rule : this.treeTraceRules) {
            if (rule.getVariables().size() != 1) {
                return false;
            }
        }

        for (final IGeneralizedRule rule : this.treeTraceRules) {
            this.definedSymbols.add(rule.getLeft().getRootSymbol());
        }

        return this.checkSymbols();
    }

    private boolean checkSymbols() {
        for (final IGeneralizedRule rule : this.treeTraceRules) {
            final TRSFunctionApplication leftFunc = rule.getLeft();
            final TRSTerm right = rule.getRight();

            if (!(right instanceof TRSFunctionApplication)) {
                return false;
            }
            final TRSFunctionApplication rightFunc = (TRSFunctionApplication) right;

            if (!this.definedSymbols.contains(rightFunc.getRootSymbol())) {
                return false;
            }

            for (final TRSTerm arg : leftFunc.getArguments()) {
                if (!this.checkTerm(arg)) {
                    return false;
                }
            }
            for (final TRSTerm arg : rightFunc.getArguments()) {
                if (!this.checkTerm(arg)) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean checkTerm(final TRSTerm arg) {
        if (arg instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) arg;
            if (this.definedSymbols.contains(func.getRootSymbol()) || func.getRootSymbol().getArity() == 0) {
                return false;
            }
        }
        return true;
    }
}
