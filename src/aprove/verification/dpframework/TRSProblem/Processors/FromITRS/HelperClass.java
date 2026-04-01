package aprove.verification.dpframework.TRSProblem.Processors.FromITRS;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A bundle of useful things.
 * @author cotto
 */
public final class HelperClass {
    /**
     * No.
     */
    private HelperClass() {
    }

    /**
     * @param newRules the new rules
     * @return a new Q termset for all LHS of the new rules
     */
    public static QTermSet getNewQ(final Collection<Rule> newRules) {
        final Collection<TRSFunctionApplication> lhs =
            new LinkedHashSet<TRSFunctionApplication>();
        for (final GeneralizedRule rule : newRules) {
            lhs.add(rule.getLeft());
        }
        return new QTermSet(lhs);
    }

    /**
     * Remove the given arguments and generate fresh names if needed.
     * @param term the old term
     * @param removePositions information positions to remove
     * @param names the name mapping
     * @param takenSymbols the function symbols that are already in use and may
     * not be used again
     * @return a new function application where some arguments may be removed
     */
    public static TRSTerm remove(final TRSTerm term,
        final CollectionMap<FunctionSymbol, Integer> removePositions,
        final Map<FunctionSymbol, FunctionSymbol> names,
        final Collection<FunctionSymbol> takenSymbols) {
        if (!(term instanceof TRSFunctionApplication)) {
            return term;
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication) term;
        final FunctionSymbol sym = fa.getRootSymbol();
        final Collection<Integer> remove = removePositions.getNotNull(sym);
        // do we already have the new symbol?
        final int newArity = sym.getArity() - remove.size();
        final String oldName = sym.getName();
        FunctionSymbol newFs = names.get(sym);

        if (newFs == null) {
            // no, so just generate a fresh one
            String newName = oldName;
            newFs = FunctionSymbol.create(newName, newArity);
            int counter = 0;
            while (takenSymbols.contains(newFs)) {
                newName = oldName + counter;
                newFs = FunctionSymbol.create(newName, newArity);
                counter++;
            }
            names.put(sym, newFs);
            takenSymbols.add(newFs);
        }

        // create an function application for the symbol
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(newArity);
        for (int i = 0; i < sym.getArity(); i++) {
            if (!remove.contains(Integer.valueOf(i))) {
                final TRSTerm arg = fa.getArgument(i);
                args.add(HelperClass.remove(arg, removePositions, names, takenSymbols));
            }
        }
        return TRSTerm.createFunctionApplication(newFs, args);
    }

    /**
     * Remove the given arguments of all terms, construct a new ITRS and return
     * it. In addition, information about renamed symbols is returned.
     * @param qtrs the qtrs
     * @param removedPositions information about arguments that can be removed
     * @return a result with a new ITRS
     */
    public static Pair<QTRSProblem, Map<FunctionSymbol, FunctionSymbol>> getResultingQTRS(final QTRSProblem qtrs,
        final CollectionMap<FunctionSymbol, Integer> removedPositions) {
        return HelperClass.getResultingQTRS(qtrs, removedPositions,
            new LinkedHashSet<FunctionSymbol>());
    }

    /**
     * Remove the given arguments of all terms, construct a new ITRS and return
     * it. In addition, information about renamed symbols is returned.
     * @param qtrs the qtrs
     * @param removedPositions information about arguments that can be removed
     * @param takenSymbols the function symbols that are already in use and may
     * not be used again
     * @return a result with a new ITRS
     */
    public static Pair<QTRSProblem, Map<FunctionSymbol, FunctionSymbol>> getResultingQTRS(final QTRSProblem qtrs,
        final CollectionMap<FunctionSymbol, Integer> removedPositions,
        final Collection<FunctionSymbol> takenSymbols) {
        // the rules of the new ITRS
        final Set<Rule> newRules =
            new LinkedHashSet<Rule>(qtrs.getR().size());

        // helper for name generation
        final Map<FunctionSymbol, FunctionSymbol> names =
            new LinkedHashMap<FunctionSymbol, FunctionSymbol>();

        // for uninteresting symbols do not change the name
        final Collection<FunctionSymbol> symbols =
            new LinkedHashSet<FunctionSymbol>();
        for (final GeneralizedRule rule : qtrs.getR()) {
            symbols.addAll(rule.getLeft().getFunctionSymbols());
            symbols.addAll(rule.getRight().getFunctionSymbols());
        }
        symbols.removeAll(removedPositions.keySet());
        for (final FunctionSymbol fs : symbols) {
            final boolean added = takenSymbols.add(fs);
            assert (added);
            names.put(fs, fs);
        }

        for (final GeneralizedRule rule : qtrs.getR()) {
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSFunctionApplication newLhs =
                (TRSFunctionApplication)
                HelperClass.remove(lhs, removedPositions, names, takenSymbols);
            final TRSTerm rhs = rule.getRight();
            TRSTerm newRhs;
            if (!rhs.isVariable()) {
                newRhs =
                    HelperClass.remove(rhs, removedPositions, names,
                        takenSymbols);
            } else {
                newRhs = rhs;
            }
            final Rule newRule = Rule.create(newLhs, newRhs);
            newRules.add(newRule);
        }
        final QTermSet newQ = HelperClass.getNewQ(newRules);
        final QTRSProblem newQtrs =
            QTRSProblem.create(ImmutableCreator.create(newRules), newQ);
        return new Pair<QTRSProblem, Map<FunctionSymbol, FunctionSymbol>>(
            newQtrs, names);
    }
}
