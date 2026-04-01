package aprove.verification.oldframework.IRSwT.Processors.TraceTermination;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Represents a way, which is basically an argument filtering
 * that removes all but one argument everywhere.
 * Additionally it may rename defined symbols (this data structure
 * allows you to rename also other symbols, but I wont use this "feature").
 * @author Matthias Hoelzel
 *
 */
public class Way {
    private final ImmutableLinkedHashMap<FunctionSymbol, Integer> remainingPosition;

    private final ImmutableLinkedHashMap<FunctionSymbol, String> renaming;

    public Way(
        final LinkedHashMap<FunctionSymbol, Integer> positions,
        final LinkedHashMap<FunctionSymbol, String> newNames)
    {
        this.remainingPosition = ImmutableCreator.create(new LinkedHashMap<FunctionSymbol, Integer>(positions));
        this.renaming = ImmutableCreator.create(new LinkedHashMap<FunctionSymbol, String>(newNames));
    }

    public TRSTerm applyWay(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return t;
        } else if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final Integer remaing = this.remainingPosition.get(f.getRootSymbol());
            if (remaing == null) {
                return null;
            } else {
                final FunctionSymbol symbol = f.getRootSymbol();
                final FunctionSymbol newSymbol;
                if (this.renaming.containsKey(symbol)) {
                    newSymbol = FunctionSymbol.create(this.renaming.get(symbol), 1);
                } else {
                    newSymbol = FunctionSymbol.create(symbol.getName(), 1);
                }
                final TRSTerm filteredArgument = this.applyWay(f.getArgument(remaing));
                if (filteredArgument == null) {
                    return null;
                } else {
                    return TRSTerm.createFunctionApplication(newSymbol, filteredArgument);
                }
            }
        }
        return null;
    }

    public static IGeneralizedRule applyWays(final IGeneralizedRule rule, final Way leftWay, final Way rightWay) {
        final TRSTerm leftInterpretation = leftWay.applyWay(rule.getLeft());
        final TRSTerm rightInterpretation = rightWay.applyWay(rule.getRight());

        assert leftInterpretation instanceof TRSFunctionApplication : "Should be function application!";
        return IGeneralizedRule.create(
            (TRSFunctionApplication) leftInterpretation,
            rightInterpretation,
            rule.getCondTerm());
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("Way:");
        for (final Entry<FunctionSymbol, Integer> e : this.remainingPosition.entrySet()) {
            sb.append("\n");
            sb.append(e.getKey().getName());
            sb.append(": ");
            sb.append(e.getValue());
            if (this.renaming.containsKey(e.getKey())) {
                sb.append(" [");
                sb.append(this.renaming.get(e.getKey()));
                sb.append("]");
            }
        }
        return sb.toString();
    }
}
