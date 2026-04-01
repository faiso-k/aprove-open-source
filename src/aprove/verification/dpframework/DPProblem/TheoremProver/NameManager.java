package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A NameManager assigns and keeps track of names of function symbols
 * with special meanings for the QDPTheoremProverProcessor. It also
 * renames function symbols from the user-supplied input whose names
 * clash with a String that is "pre-defined" in our theorem prover.
 *
 * @author fuhs
 */
public class NameManager {

    // used symbol names
    private final Set<String> unfreshNames;

    private FunctionSymbol falseSym;
    private FunctionSymbol trueSym;
    private FunctionSymbol andSym;
    private FunctionSymbol orSym;

    private TRSFunctionApplication falseApp;
    private TRSFunctionApplication trueApp;

    // map sort names to the corresponding witness symbols
    private Map<String, FunctionSymbol> witnessSymbolsForSorts;

    // map sort names to the corresponding equals symbols
    private Map<String, FunctionSymbol> equalSymbolsForSorts;

    // symbol renaming for input terms to avoid clashes between predefined
    // names of our theorem prover and the function symbol names chosen by
    // the user
    private Map<FunctionSymbol, FunctionSymbol> inputSymbolRenaming;

    // postfix index for generating new names
    private int appendIndex = 0;

    // predefined names which are hard-coded into our theorem prover ;-/
    private static final String PREDEF_FALSE = "false";
    private static final String PREDEF_TRUE = "true";
    private static final String PREDEF_AND = "and";
    private static final String PREDEF_OR = "or";
    private static final String PREDEF_NOT = "not";
    private static final String PREDEF_IS_A_TRUE = "isa_true";
    private static final String PREDEF_IS_A_FALSE = "isa_false";
    private static final String PREDEF_EQUAL_BOOL = "equal_bool";

    // default prefixes for generated names
    private static final String DEFAULT_WITNESS_PREFIX = "witness_";
    private static final String DEFAULT_EQUAL_PREFIX = "equal_";

    // default prefix for fresh variables
    private static final String DEFAULT_VAR_PREFIX = "v";

    // default postfix for renamed function symbols
    private static final String DEFAULT_NEWFUN_POSTFIX = "_renamed";

    /**
     * Only gathers the names from the parameters and initializes some fields.
     * Initialization of predefined symbols should be done outside.
     *
     * @param usedFunctionSymbols
     * @param usedVariables
     */
    private NameManager(Set<FunctionSymbol> usedFunctionSymbols, Set<TRSVariable> usedVariables) {
        Set<String> names = CollectionUtils.getNames(usedFunctionSymbols);
        names.addAll(CollectionUtils.getNames(usedVariables));
        names.add(NameManager.PREDEF_FALSE);
        names.add(NameManager.PREDEF_TRUE);
        names.add(NameManager.PREDEF_AND);
        names.add(NameManager.PREDEF_OR);
        names.add(NameManager.PREDEF_NOT);
        names.add(NameManager.PREDEF_IS_A_FALSE);
        names.add(NameManager.PREDEF_IS_A_TRUE);
        names.add(NameManager.PREDEF_EQUAL_BOOL);
        this.witnessSymbolsForSorts = new LinkedHashMap<String, FunctionSymbol>();
        this.equalSymbolsForSorts = new LinkedHashMap<String, FunctionSymbol>();
        this.unfreshNames = names;
    }

    /**
     * @param usedFunctionSymbols - function symbols that are not fresh anymore
     *  (e.g. because they were part of the input problem)
     * @param usedVariables - variables that are not fresh any more
     */
    public static NameManager create(Set<FunctionSymbol> usedFunctionSymbols,
            Set<TRSVariable> usedVariables) {
        NameManager res = new NameManager(usedFunctionSymbols, usedVariables);
        res.initPredefs(usedFunctionSymbols);
        return res;
    }

    /**
     * Initializes the renaming of input function symbols to avoid clashes
     * with the predefined names hard-coded into our theorem prover.
     */
    private void initPredefs(Set<FunctionSymbol> usedFunctionSymbols) {

        Map<FunctionSymbol, FunctionSymbol> protoRenaming =
            new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        // beware of clashes between f/2 and f/1
        Set<String> seenFNames = new LinkedHashSet<String>();
        for (FunctionSymbol f : usedFunctionSymbols) {
            String fName = f.getName();
            String newName = null;
            if (NameManager.hasPredefinedName(f)) {
                // the user chose a name like "and" or "true"
                newName = this.getFreshName(fName + NameManager.DEFAULT_NEWFUN_POSTFIX);
            } else if (seenFNames.contains(fName)) {
                // arity clash for f
                newName = this.getFreshName(fName + NameManager.DEFAULT_NEWFUN_POSTFIX);
            }
            seenFNames.add(fName);
            if (newName != null) {
                seenFNames.add(newName);
                FunctionSymbol newSym = FunctionSymbol.create(newName, f.getArity());
                protoRenaming.put(f, newSym);
            }
        }
        this.inputSymbolRenaming = protoRenaming;

        // false
        this.falseSym = FunctionSymbol.create(NameManager.PREDEF_FALSE, 0);
        this.falseApp = TRSTerm.createFunctionApplication(this.falseSym, TRSTerm.EMPTY_ARGS);

        // true
        this.trueSym = FunctionSymbol.create(NameManager.PREDEF_TRUE, 0);
        this.trueApp = TRSTerm.createFunctionApplication(this.trueSym, TRSTerm.EMPTY_ARGS);

        // and
        this.andSym = FunctionSymbol.create(NameManager.PREDEF_AND, 2);

        // or
        this.orSym = FunctionSymbol.create(NameManager.PREDEF_OR, 2);
    }



    private static boolean hasPredefinedName(FunctionSymbol f) {
        String fName = f.getName();
        return fName.equals(NameManager.PREDEF_TRUE)
            || fName.equals(NameManager.PREDEF_FALSE)
            || fName.equals(NameManager.PREDEF_AND)
            || fName.equals(NameManager.PREDEF_OR)
            || fName.equals(NameManager.PREDEF_NOT)
            || fName.equals(NameManager.PREDEF_IS_A_TRUE)
            || fName.equals(NameManager.PREDEF_IS_A_FALSE)
            || fName.equals(NameManager.PREDEF_EQUAL_BOOL);
    }

    /**
     * @param rulesWithPotentiallyClashingSymbols
     * @return x: a set of rules where function symbols that clash with
     *  predefined symbol names or with multiple arities have been
     *  renamed; may or may not be the same object as
     *  rulesWithPotentiallyClashingSymbols<br>
     *  y: a mapping from cleaned ruled to original rules
     */
    public Pair<ImmutableSet<Rule>, Map<Rule, Rule>> cleanSymbolsInRules(ImmutableSet<Rule> rulesWithPotentiallyClashingSymbols) {
        Map<Rule, Rule> resY = new LinkedHashMap<Rule, Rule>();
        if (this.inputSymbolRenaming.isEmpty()) {
            for (Rule rule : rulesWithPotentiallyClashingSymbols) {
                resY.put(rule, rule);
            }
            return new Pair<ImmutableSet<Rule>, Map<Rule, Rule>>(
                    rulesWithPotentiallyClashingSymbols, resY);
        }
        Set<Rule> protoResX = new LinkedHashSet<Rule>();
        for (Rule rule : rulesWithPotentiallyClashingSymbols) {
            Rule newRule = rule.replaceAllFunctionSymbols(this.inputSymbolRenaming);
            protoResX.add(newRule);
            resY.put(newRule, rule);
        }
        return new Pair<ImmutableSet<Rule>, Map<Rule, Rule>>(
                ImmutableCreator.create(protoResX), resY);
    }

    public FunctionSymbol establishWitnessTerm(Set<FunctionSymbol> constructors,
            String sortName) {
        // First check whether we already have a witness.
        FunctionSymbol witness = this.witnessSymbolsForSorts.get(sortName);
        if (witness != null) {
            return witness;
        }

        // Choose lexicographically smallest constant as witness term
        for (FunctionSymbol funSym : constructors) {
            if (witness == null && funSym.getArity() == 0) {
                witness = funSym;
            }
            else if (witness != null && funSym.getArity() == 0) {
                if (funSym.getName().compareTo(witness.getName()) < 0) {
                    witness = funSym;
                }
            }
        }
        // Here we have an "empty" sort, we must add a new constant.
        if (witness == null) {
            int i = 0;
            String witnessNameCand = NameManager.DEFAULT_WITNESS_PREFIX + sortName;
            while (this.unfreshNames.contains(witnessNameCand)) {
                witnessNameCand = NameManager.DEFAULT_WITNESS_PREFIX + sortName + '_' + (i++);
            }
            witness = FunctionSymbol.create(witnessNameCand, 0);
            constructors.add(witness);
            this.unfreshNames.add(witnessNameCand);
        }
        this.witnessSymbolsForSorts.put(sortName, witness);
        return witness;
    }

    /**
     * @param sortName
     * @return witness term for the sort with name sortName if it has already
     *  been established; null otherwise
     */
    public FunctionSymbol getWitnessTerm(String sortName) {
        FunctionSymbol witness = this.witnessSymbolsForSorts.get(sortName);
        return witness;
    }


    public FunctionSymbol getEqualsSymbol(String sortName) {
        // First check whether we already have an equals symbol for the sort.
        FunctionSymbol eq = this.equalSymbolsForSorts.get(sortName);
        if (eq != null) {
            return eq;
        }

        String eqNameCand;
        if (sortName.equals(QDPTheoremProverProcessor.BOOL_SORT)) {
            eqNameCand = NameManager.PREDEF_EQUAL_BOOL;

        } else {
            int i = 0;
            eqNameCand = NameManager.DEFAULT_EQUAL_PREFIX + sortName;
            while (this.unfreshNames.contains(eqNameCand)) {
                eqNameCand = NameManager.DEFAULT_EQUAL_PREFIX + sortName + '_' + (i++);
            }
        }
        eq = FunctionSymbol.create(eqNameCand, 2);
        this.unfreshNames.add(eqNameCand);
        this.equalSymbolsForSorts.put(sortName, eq);
        return eq;
    }

    /**
     * @param k
     * @return max(k,0) variable with pairwise different fresh names
     *  (they will not be considered fresh afterwards)
     */
    public ImmutableArrayList<TRSVariable> getFreshVariablesImmutable(int k) {
        ArrayList<TRSVariable> vars = this.getFreshVariables(k);
        return ImmutableCreator.create(vars);
    }

    /**
     * @param k
     * @return max(k,0) variable with pairwise different fresh names
     *  (they will not be considered fresh afterwards); the result may
     *  be modified
     */
    public ArrayList<TRSVariable> getFreshVariables(int k) {
        ArrayList<TRSVariable> vars = new ArrayList<TRSVariable>(k);
        for (int i = k-1; i >= 0; --i) {
            TRSVariable v = this.getFreshVariable();
            vars.add(v);
        }
        return vars;
    }

    /**
     * @return a variable with a fresh name (which will not be considered
     *  fresh afterwards)
     */
    public TRSVariable getFreshVariable() {
        String cand;
        do {
            cand = NameManager.DEFAULT_VAR_PREFIX + (this.appendIndex++);
        } while (this.unfreshNames.contains(cand));
        this.unfreshNames.add(cand);
        TRSVariable v = TRSTerm.createVariable(cand);
        return v;
    }

    /**
     * @param proposal
     * @return a fresh name that looks very similar to proposal
     *  (actually, proposal is tried first, only then do we try to
     *  append something) -- will not be considered fresh afterwards
     */
    public String getFreshName(String proposal) {
        String res = proposal;
        while (this.unfreshNames.contains(res)) {
            res = proposal + (this.appendIndex++);
        }
        this.unfreshNames.add(res);
        return res;
    }

    /**
     * @param candidate
     * @return whether candidate would be fresh according to this
     */
    public boolean isFresh(String candidate) {
        boolean res = ! this.unfreshNames.contains(candidate);
        return res;
    }

    /**
     * @param name
     * @return if the name was newly considered to be unfresh
     *  (i.e., if it was an actual addition to the internal storage of
     *  unfresh names)
     */
    public boolean addUnfreshName(String name) {
        boolean res = this.unfreshNames.add(name);
        return res;
    }

    /**
     * @return the falseName
     */
    public String getFalseName() {
        return NameManager.PREDEF_FALSE;
    }

    /**
     * @return the trueName
     */
    public String getTrueName() {
        return NameManager.PREDEF_TRUE;
    }

    /**
     * @return the andName
     */
    public String getAndName() {
        return NameManager.PREDEF_AND;
    }

    /**
     * @return the orName
     */
    public String getOrName() {
        return NameManager.PREDEF_OR;
    }

    /**
     * @return the notName
     */
    public String getNotName() {
        return NameManager.PREDEF_NOT;
    }

    /**
     * @return the isATrueName
     */
    public String getIsATrueName() {
        return NameManager.PREDEF_IS_A_TRUE;
    }

    /**
     * @return the isAFalseName
     */
    public String getIsAFalseName() {
        return NameManager.PREDEF_IS_A_FALSE;
    }

    /**
     * @return the falseSym
     */
    public FunctionSymbol getFalseSym() {
        return this.falseSym;
    }

    /**
     * @return the trueSym
     */
    public FunctionSymbol getTrueSym() {
        return this.trueSym;
    }

    /**
     * @return the andSym
     */
    public FunctionSymbol getAndSym() {
        return this.andSym;
    }

    /**
     * @return the orSym
     */
    public FunctionSymbol getOrSym() {
        return this.orSym;
    }

    /**
     * @return the falseApp
     */
    public TRSFunctionApplication getFalseApp() {
        return this.falseApp;
    }

    /**
     * @return the trueApp
     */
    public TRSFunctionApplication getTrueApp() {
        return this.trueApp;
    }
}
