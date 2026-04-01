package aprove.input.Programs.prolog.processors;

import java.util.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A special fresh name generator which ensures that for each name n
 * returned by getFreshName, the names n + IN and n + OUT are also fresh
 * (and reserved).
 *
 * So, if we want to generate in- and out-Symbols for a Symbol s, we just do
 * getFreshName(s.getName()) and may use safely
 * s + {@link PrologToPiTRSTransformer}.IN and
 * s + {@link PrologToPiTRSTransformer}.OUT afterwards.
 */
public class PrologFNG implements FreshNameChecker {

    /**
     * Already mapped names
     */
    private final Map<String, String> memory =
        new HashMap<String, String>();

    private final Set<String> used;

    private final NameGenerator ng;

    /**
     * The ending for out function symbols.
     */
    public static final String OUT = "_out";

    /**
     * The ending for in function symbols.
     */
    public static final String IN = "_in";

    public PrologFNG(Set<String> used, NameGenerator ng) {
        this.used = new HashSet<String>(used);
        this.ng = ng;
    }

    public String getFreshName(String old, boolean useMemory) {
        if (useMemory) {
            String cached = this.memory.get(old);
            if (cached != null) {
                return cached;
            }
        }

        String newBase = this.ng.getNewName(old, this);
        this.used.add(newBase);
        this.used.add(newBase + PrologFNG.IN);
        this.used.add(newBase + PrologFNG.OUT);
        if (useMemory) {
            this.memory.put(old, newBase);
        }
        return newBase;
    }

    @Override
    public boolean isUnused(String name) {
        return
        !(
                this.used.contains(name) ||
                this.used.contains(name + PrologFNG.IN) ||
                this.used.contains(name + PrologFNG.OUT)
        );
    }

    /**
     * Creates a new FunctionSymbol for the specified term to use as in
     * symbol for GeneralizedRules. The FunctionSymbol has the arity of
     * this term. Its name is the result of the FreshNameGenerator's
     * getFreshName() method with the term's name followed by
     * PrologToPiTRSTransformer.IN as argument. To be useful, the
     * FreshNameGenerator should have its useMemory flag set to true.
     * @param term The PrologTerm from which to build a symbol.
     * @return A new FunctionSymbol for this term used as in symbol in
     *         GeneralizedRules.
     */
    public FunctionSymbol createInFunctionSymbol(PrologTerm term) {
        return FunctionSymbol.create(
            this.getInSymbolName(term.getName()),
            term.getArity()
        );
    }

    /**
     * Creates a new FunctionSymbol for the specified term to use as out
     * symbol for GeneralizedRules. The FunctionSymbol has the arity of
     * this term. Its name is the result of the FreshNameGenerator's
     * getFreshName() method with the term's name followed by
     * PrologToPiTRSTransformer.OUT as argument. To be useful, the
     * FreshNameGenerator should have its useMemory flag set to true.
     * @param term The PrologTerm from which to build a symbol.
     * @return A new FunctionSymbol for this term used as out symbol in
     *         GeneralizedRules.
     */
    public FunctionSymbol createOutFunctionSymbol(PrologTerm term) {
        return FunctionSymbol.create(
            this.getOutSymbolName(term.getName()),
            term.getArity()
        );
    }

    public String getInSymbolName(String oldName) {
        return this.getFreshName(oldName, true) + PrologFNG.IN;
    }

    public String getOutSymbolName(String oldName) {
        return this.getFreshName(oldName, true) + PrologFNG.OUT;
    }

}