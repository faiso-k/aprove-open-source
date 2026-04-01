package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author micpar
 * @version $Id$
 */

public class SortCalculator {

    /*
     * Attributes
     */
    private ImmutableMap<FunctionSymbol, ImmutableArrayList<Sort>> funInputSortMap  = null;
    private ImmutableMap<FunctionSymbol, Sort>                     funOutputSortMap = null;
    private ImmutableMap<TRSVariable, Sort>                           variableSortMap  = null;

    private ImmutableSet<Sort>                                     sorts            = null;
    private Sort                                                   bool             = null;

    private TypeAssumption                                         typeAssumption   = null;
    private ImmutableSet<Rule>                                     R                = null;

    private NameManager                                            nameManager;

    /**
     * Creates a new SortCalculator object and calculates the sorts.
     *
     * @param typeAssumption
     * @param R
     */
    public SortCalculator(TypeAssumption typeAssumption, ImmutableSet<Rule> R, NameManager nameManager) {
        this.typeAssumption = typeAssumption;
        this.R = R;
        this.nameManager = nameManager;
        this.calculateSorts();
    }

    /*
     * Getters
     */

    /**
     * @return Mapping of variable (not type variable) to sort
     */
    public ImmutableMap<TRSVariable, Sort> getVariableSortMap() {
        return this.variableSortMap;
    }

    /**
     * @return Mapping of all function symbols to input sorts
     */
    public ImmutableMap<FunctionSymbol, ImmutableArrayList<Sort>> getFunInputSortMap() {
        return this.funInputSortMap;
    }

    /**
     * @return Mapping of all function symbols to output sorts
     */
    public ImmutableMap<FunctionSymbol, Sort> getFunOutputSortMap() {
        return this.funOutputSortMap;
    }

    /**
     * @return Sorts
     */
    public ImmutableSet<Sort> getSorts() {
        return this.sorts;
    }

    /**
     * @return boolean sort
     */
    public Sort getBool() {
        return this.bool;
    }

    /**
     * Adds defined function to allfun map
     *
     * @param defFunSym
     * @param inputSorts
     * @param outputSort
     */
    public void addDefFunctionSymbolToMaps(FunctionSymbol defFunSym, ImmutableArrayList<Sort> inputSorts, Sort outputSort) {

        Map<FunctionSymbol, ImmutableArrayList<Sort>> inputMap = new LinkedHashMap<FunctionSymbol, ImmutableArrayList<Sort>>();
        inputMap.put(defFunSym, inputSorts);
        inputMap.putAll(this.funInputSortMap);
        this.funInputSortMap = ImmutableCreator.create(inputMap);

        Map<FunctionSymbol, Sort> outputMap = new LinkedHashMap<FunctionSymbol, Sort>();
        outputMap.put(defFunSym, outputSort);
        outputMap.putAll(this.funOutputSortMap);
        this.funOutputSortMap = ImmutableCreator.create(outputMap);
    }

    /**
     * Adds variable to variable map
     *
     * @param var
     * @param sort
     */
    public void addVariableToMap(TRSVariable var, Sort sort) {
        Map<TRSVariable, Sort> varMap = new LinkedHashMap<TRSVariable, Sort>();
        varMap.putAll(this.variableSortMap);
        varMap.put(var, sort);
        this.variableSortMap = ImmutableCreator.create(varMap);
    }

    /**
     * @param name
     * @return Sort with name name
     */
    public Sort getSortByName(String name) {
        for (Sort sort : this.sorts) {
            if (name.equals(sort.getName())) {
                return sort;
            }
        }
        return null;
    }

    /*
     * private methods
     */

    /*
     * Compute sorts and save them together with type variables from type
     * assumption. Connect function symbols with according sorts.
     */
    private void calculateSorts() {
        // Calculate the constructor and defined function symbols
        RuleAnalysis<Rule> analysis = new RuleAnalysis<Rule>(this.R, IDPPredefinedMap.EMPTY_MAP);
        ImmutableSet<FunctionSymbol> defSyms = analysis.getDefinedSymbols();
        ImmutableSet<FunctionSymbol> funSyms = analysis.getFunctionSymbols();
        Set<FunctionSymbol> conSyms = new LinkedHashSet<FunctionSymbol>();

        for (FunctionSymbol funSym : funSyms) {
            if (!defSyms.contains(funSym)) {
                conSyms.add(funSym);
            }
        }

        // Calculate sorts and map variables, constructors and defined functions
        // to them
        Set<Sort> sorts = new LinkedHashSet<Sort>();
        Map<TRSVariable, Sort> variableMap = new LinkedHashMap<TRSVariable, Sort>();
        Map<FunctionSymbol, Sort> funOutputMap = new LinkedHashMap<FunctionSymbol, Sort>();

        Set<TRSVariable> typeVars = this.typeAssumption.getTypeVariables();

        FunctionSymbol falseSym = this.nameManager.getFalseSym();
        FunctionSymbol trueSym = this.nameManager.getTrueSym();
        Map<TRSVariable, Sort> typeVariableMap = new LinkedHashMap<TRSVariable, Sort>();
        for (TRSVariable typeVar : typeVars) {
            // Create sort here
            Map<String, Integer> symbols = this.typeAssumption.getSymbolsForTypeVariable(typeVar);
            Set<FunctionSymbol> constructors = new LinkedHashSet<FunctionSymbol>();
            for (Map.Entry<String, Integer> entry : symbols.entrySet()) {
                FunctionSymbol conSym = FunctionSymbol.create(entry.getKey(), entry.getValue());
                if (conSyms.contains(conSym)) {
                    constructors.add(conSym);
                }
            }

            Sort newSort;

            if (! (constructors.size() == 2 && constructors.contains(trueSym)
                    && constructors.contains(falseSym))) {
                String sortName = QDPTheoremProverProcessor.SORT_PREFIX
                                    + '[' + typeVar.getName() + ']';
                FunctionSymbol witnessTerm = this.nameManager.establishWitnessTerm(constructors, sortName);
                String witnessName = witnessTerm.getName();
                if (symbols.get(witnessName) == null) {
                    symbols.put(witnessName, 0);
                }
                if (!funSyms.contains(witnessTerm)) {
                    Set<FunctionSymbol> temp = new LinkedHashSet<FunctionSymbol>(funSyms);
                    temp.add(witnessTerm);
                    funSyms = ImmutableCreator.create(temp);
                }
                constructors.add(witnessTerm);
                newSort = new Sort(sortName, ImmutableCreator.create(constructors), witnessTerm);


                sorts.add(newSort);
                typeVariableMap.put(typeVar, newSort);

                // Connect sort and function or variable symbol
                for (Map.Entry<String, Integer> entry : symbols.entrySet()) {
                    FunctionSymbol symbol = FunctionSymbol.create(entry.getKey(), entry.getValue());
                    if (funSyms.contains(symbol)) {
                        funOutputMap.put(symbol, newSort);
                    }
                    else {
                        variableMap.put(TRSTerm.createVariable(entry.getKey()), newSort);
                    }
                }
            }
        }

        // previously: may or may not contain bool sort
        // now:        for sure does not contain bool sort
        this.sorts = ImmutableCreator.create(sorts);

        // Bool type must exist
        Set<FunctionSymbol> constructors = new LinkedHashSet<FunctionSymbol>();
        constructors.add(this.nameManager.getTrueSym());
        constructors.add(this.nameManager.getFalseSym());
        this.bool = new Sort(QDPTheoremProverProcessor.BOOL_SORT,
                ImmutableCreator.create(constructors),
                this.nameManager.getFalseSym());

        this.variableSortMap = ImmutableCreator.create(variableMap);
        this.funOutputSortMap = ImmutableCreator.create(funOutputMap);

        // Calculate sorts for the arguments of all functions
        Map<FunctionSymbol, ImmutableArrayList<Sort>> funInputMap = new LinkedHashMap<FunctionSymbol, ImmutableArrayList<Sort>>();

        for (FunctionSymbol funSym : funSyms) {
            if (funSym.getArity() > 0) {
                Signature sig = this.typeAssumption.getSignatureForSymbol(funSym.getName());
                ArrayList<Sort> sortList = new ArrayList<Sort>();
                for (TRSTerm typeVar : sig.getInputTypes()) {
                    if (typeVar.isVariable()) {
                        sortList.add(typeVariableMap.get((TRSVariable) typeVar));
                    }
                }
                funInputMap.put(funSym, ImmutableCreator.create(sortList));
            }
        }

        this.funInputSortMap = ImmutableCreator.create(funInputMap);
    }
}
