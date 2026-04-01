package aprove.verification.oldframework.IRSwT.Utils;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Collect all occuring symbols and their names.
 * @author Matthias Hoelzel
 */
public class SymbolNamesCollector {
    /** Set of rules to be analyzed */
    private final Set<IGeneralizedRule> rules;

    /** Set of names that occur as symbols */
    private final LinkedHashSet<String> symbolNames;

    /** Set of symbols */
    private final LinkedHashSet<FunctionSymbol> symbols;

    /** Set of defined symbols */
    private final LinkedHashSet<FunctionSymbol> definedSymbols;

    /**
     * Constructor!
     * @param inputRules set of rules
     */
    public SymbolNamesCollector(final Set<IGeneralizedRule> inputRules) {
        this.rules = inputRules;
        this.symbolNames = new LinkedHashSet<>();
        this.symbols = new LinkedHashSet<>();
        this.definedSymbols = new LinkedHashSet<>();
        this.collect();
    }

    /**
     * Getter for the rules
     * @return set of rules
     */
    public Set<IGeneralizedRule> getRules() {
        return this.rules;
    }

    /**
     * Getter for the symbol names.
     * @return set of strings
     */
    public LinkedHashSet<String> getSymbolNames() {
        return this.symbolNames;
    }

    /**
     * Getter for the symbols
     * @return set of symbols
     */
    public LinkedHashSet<FunctionSymbol> getSymbols() {
        return this.symbols;
    }

    /**
     * Getter for the defined symbols
     * @return set of defined symbols
     */
    public LinkedHashSet<FunctionSymbol> getDefinedSymbols() {
        return this.definedSymbols;
    }

    /**
     * Collects all the information.
     */
    private void collect() {
        for (final IGeneralizedRule rule : this.rules) {
            this.registerSymbols(rule.getLeft());
            this.registerSymbols(rule.getRight());
            final TRSFunctionApplication left = rule.getLeft();
            this.definedSymbols.add(left.getRootSymbol());
        }
    }

    /**
     * Registers the symbols occurring in t.
     * @param t some term
     */
    private void registerSymbols(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                this.symbols.add(sym);
                this.symbolNames.add(sym.getName());
                for (final TRSTerm arg : func.getArguments()) {
                    this.registerSymbols(arg);
                }
            }
        }
    }

}
