package aprove.verification.dpframework.TRSProblem.Processors.FromITRS;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.dpframework.BasicStructures.*;
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
    private final CollectionMap<FunctionSymbol, Integer> rem;

    /**
     * A map knowing the new name for each function symbol.
     */
    private final Map<FunctionSymbol, FunctionSymbol> newNames;

    /**
     * A new proof.
     * @param removedArgs information about removed arguments.
     * @param names mapping of function symbols
     */
    public ArgumentsRemovalProof(
            final CollectionMap<FunctionSymbol, Integer> removedArgs,
        final Map<FunctionSymbol, FunctionSymbol> names) {
        this.rem = removedArgs;
        this.newNames = names;
    }

    /**
     * @param o some export util
     * @param sb a string builder where the proof will be appended
     */
    public void export(final Export_Util o,
        final StringBuilder sb) {
        final Collection<Rule> rules = new LinkedHashSet<Rule>();
        for (final Map.Entry<FunctionSymbol, Collection<Integer>> entry : this.rem.entrySet()) {
            final Collection<Integer> removed = entry.getValue();
            final FunctionSymbol fsLeft = entry.getKey();
            final FunctionSymbol fsRight = this.newNames.get(fsLeft);

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
        sb.append("We removed arguments according to the following replacements:");
        sb.append(o.linebreak());
        sb.append(o.set(rules, Export_Util.RULES));
    }
}
