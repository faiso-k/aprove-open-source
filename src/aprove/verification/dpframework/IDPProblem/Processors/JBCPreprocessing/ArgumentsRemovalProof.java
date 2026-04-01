package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A proof that will be used to denote which arguments are deleted.
 * @author cotto
 */
public abstract class ArgumentsRemovalProof extends DefaultProof {
    /**
     * The arguments that are removed.
     */
    private final Collection<Rule> rem;

    /**
     * The problem that has been processed
     */
    private final ITRSProblem itrsProblem;

    /**
     * A new proof.
     * @param itrsProblemParam the problem that has been processed
     * @param removedArgs information about removed arguments.
     * @param names mapping of function symbols
     */
    public ArgumentsRemovalProof(
            final ITRSProblem itrsProblemParam,
            final CollectionMap<FunctionSymbol, Integer> removedArgs,
        final Map<FunctionSymbol, FunctionSymbol> names) {
        this.itrsProblem = itrsProblemParam;
        this.rem = ArgumentsRemovalProof.getFilterRules(removedArgs, names);
    }

    /**
     * A new proof.
     * @param itrsProblemParam the problem that has been processed
     * @param removedArgsRules information about removed arguments.
     */
    public ArgumentsRemovalProof(
            final ITRSProblem itrsProblemParam,
            final Collection<Rule> removedArgs) {
        this.itrsProblem = itrsProblemParam;
        this.rem = removedArgs;
    }


    /**
     * @param o some export util
     * @param sb a string builder where the proof will be appended
     */
    public void export(final Export_Util o,
        final StringBuilder sb) {
        sb.append("We removed arguments according to the following replacements:");
        sb.append(o.linebreak());
        sb.append(o.set(this.rem, Export_Util.RULES));
    }

    /**
     * @param positionsToRemove some map describing positions to be removed
     *  for each function symbol
     * @return a list of rewrite rules that simulate the argument removal.
     */
    public static Collection<Rule> getFilterRules(
            final CollectionMap<FunctionSymbol, Integer> positionsToRemove,
            final Map<FunctionSymbol, FunctionSymbol> newNames) {
        final Collection<Rule> rules = new LinkedList<Rule>();
        for (final Map.Entry<FunctionSymbol, Collection<Integer>> entry : positionsToRemove.entrySet()) {
            final Collection<Integer> removed = entry.getValue();
            final FunctionSymbol fsLeft = entry.getKey();
            final FunctionSymbol fsRight;
            if (newNames != null && newNames.containsKey(fsLeft)) {
                fsRight = newNames.get(fsLeft);
            } else {
                fsRight = FunctionSymbol.create(fsLeft.getName(), fsLeft.getArity() - removed.size());
            }
            assert (fsRight != null);

            if (!removed.isEmpty()) {
                final int arityLeft = fsLeft.getArity();
                final ArrayList<TRSTerm> argsLeft = new ArrayList<TRSTerm>(arityLeft);
                final ArrayList<TRSTerm> argsRight =
                    new ArrayList<TRSTerm>(fsLeft.getArity());

                for (int i = 0; i < arityLeft; i++) {
                    final TRSVariable newVar =
                        TRSTerm.createVariable(TRSTerm.STANDARD_PREFIX
                            + (i + 1));
                    argsLeft.add(newVar);
                    if (!removed.contains(Integer.valueOf(i))) {
                        argsRight.add(newVar);
                    }
                }
                final TRSFunctionApplication faLeft =
                    TRSTerm.createFunctionApplication(fsLeft,
                        argsLeft);
                final TRSFunctionApplication faRight =
                    TRSTerm.createFunctionApplication(fsRight,
                        argsRight);
                final Rule replacement = Rule.create(faLeft, faRight);
                rules.add(replacement);
            }
        }
        return rules;
    }

    /**
     * @return the problem that has been processed
     */
    public ITRSProblem getItrsProblem() {
        return this.itrsProblem;
    }
}
