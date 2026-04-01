package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.*;
import aprove.input.Programs.fp.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Syntax.Sort;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author micpar
 * @version $Id: ProgramInitializer.java,v 1.16 2009/01/19 15:48:53 mpluecker
 *          Exp $
 */
public class ProgramInitializer {

    /*
     * attributes
     */
    private ImmutableSet<ConditionalRule> R = null;
    private SortCalculator sortCalculator = null;
    private NameManager nameManager;

    /*
     * constructor
     */

    /**
     * @param condRules,
     *            set of rules to be added to the program.
     * @param sortCalculator,
     *            object containing the sorts.
     */
    private ProgramInitializer(
        ImmutableSet<ConditionalRule> condRules,
        SortCalculator sortCalculator,
        NameManager nameManager
    ) {
        this.R = condRules;
        this.sortCalculator = sortCalculator;
        this.nameManager = nameManager;
    }

    /**
     * Creates a new instance of ProgramInitializer and initializes Field R.
     *
     * @param condUsableRules,
     *            set of rules to be added to the program.
     * @param sortCalculator,
     *            object containing the sorts.
     * @return
     */
    public static ProgramInitializer create(
        ImmutableSet<ConditionalRule> condUsableRules,
        SortCalculator sortCalculator,
        NameManager nameManager
    ) {
        return new ProgramInitializer(condUsableRules, sortCalculator, nameManager);
    }

    /**
     * Returns a newly created Program made from input rules.
     *
     * @return Initialized program object.
     */
    public Program createAndInitializeProgram() {
        // Create empty program and add Constructor-Symbols
        Program prgrm = Program.create();
        prgrm = this.addConstructorsToProgram(prgrm);
        // Add selectors, isa_something and equals_something functions here
        prgrm = this.addPredefinedFunctionsForConstructors(prgrm);
        // Here we add the Rules in R to the program
        prgrm = this.addRulesToProgram(prgrm, this.R);
        return prgrm;
    }

    /*
     * private methods
     */

    /*
     * Add all rules to the program
     */
    private Program addRulesToProgram(Program prgrm, ImmutableSet<ConditionalRule> R) {
        // Declare defined function symbols here.
        RuleAnalysis<aprove.verification.dpframework.BasicStructures.Rule> analysis =
            new RuleAnalysis<aprove.verification.dpframework.BasicStructures.Rule>(
                ConditionalRule.unwrap(R),
                IDPPredefinedMap.EMPTY_MAP
            );
        ImmutableSet<aprove.verification.oldframework.BasicStructures.FunctionSymbol> defFuns = analysis.getDefinedSymbols();
        for (aprove.verification.oldframework.BasicStructures.FunctionSymbol funSym : defFuns) {
            try {
                // Add defined function symbol to program
                // Compute input sorts here
                List<Sort> argSorts = new Vector<Sort>();
                for (int index = 0; index < funSym.getArity(); index++) {
                    // IMPORTANT: EVERY single function symbol has to have
                    // sorts!!!! Otherwise it is going to crash here.
                    if (Globals.useAssertions) {
                        if (Globals.DEBUG_MICPAR) {
                            if (this.sortCalculator.getFunInputSortMap().get(funSym).size() != funSym.getArity()) {
                                System.out.println(funSym);
                            }
                        }
                        assert (this.sortCalculator.getFunInputSortMap().get(funSym).size() == funSym.getArity());
                    }
                    String name = this.sortCalculator.getFunInputSortMap().get(funSym).get(index).getName();
                    argSorts.add(prgrm.getSort(name));
                }
                // Here the function symbol in the old framework is created with
                // the correct input and output sorts
                if (Globals.useAssertions) {
                    if (Globals.DEBUG_MICPAR) {
                        if (this.sortCalculator.getFunOutputSortMap().get(funSym) == null) {
                            System.out.println(funSym);
                        }
                    }
                    assert (this.sortCalculator.getFunOutputSortMap().get(funSym) != null);
                }
                prgrm.addDefFunctionSymbol(DefFunctionSymbol.create(funSym.getName(), argSorts, prgrm.getSort(this.sortCalculator
                        .getFunOutputSortMap().get(funSym).getName())));
            }
            catch (ProgramException e) {
                e.printStackTrace();
            }
        }

        // Convert new rules to rules suitable for the THMProver.
        Set<Rule> oldRules = this.convertNewRulesToOldRules(prgrm, R);
        for (Rule rule : oldRules) {
            prgrm.addRule(rule);
        }

        return prgrm;
    }

    /*
     * Convert new rules to old ones
     */
    private Set<Rule> convertNewRulesToOldRules(Program prgrm, ImmutableSet<ConditionalRule> R) {
        Set<Rule> newSet = new LinkedHashSet<Rule>();
        Set<aprove.verification.oldframework.BasicStructures.FunctionSymbol> constrSymbols =
            new LinkedHashSet<aprove.verification.oldframework.BasicStructures.FunctionSymbol>(
                this.computeConstrSymbols(ConditionalRule.unwrap(R))
            );
        for (ConditionalRule rule : R) {
            // Check if LHS of Rule is linear, if not then bail out here.
            if (!rule.getLeft().isLinear()) {
                throw new RuntimeException("Rule: " + rule.toString() + " not linear");
            }
            // Convert new rules to old rules
            // Here compute conditions
            List<Rule> conds = new Vector<Rule>();
            if (rule.getConditions() != null) {
                Set<aprove.verification.dpframework.BasicStructures.Rule> temp =
                    new LinkedHashSet<aprove.verification.dpframework.BasicStructures.Rule>(rule.getConditions());
                temp.addAll(ConditionalRule.unwrap(R));
                constrSymbols.addAll(this.computeConstrSymbols(ImmutableCreator.create(temp)));
                for (aprove.verification.dpframework.BasicStructures.Rule condRule : rule.getConditions()) {
                    conds.add(
                        aprove.verification.oldframework.Rewriting.Rule.create(
                            this.convertNewTermToOldTerm(prgrm, condRule.getLeft(), constrSymbols),
                            this.convertNewTermToOldTerm(prgrm, condRule.getRight(), constrSymbols)
                        )
                    );
                }
            }
            // Here the actual rule is created
            // First case: without conditions
            if (conds.isEmpty()) {
                newSet.add(
                    aprove.verification.oldframework.Rewriting.Rule.create(
                        this.convertNewTermToOldTerm(prgrm, rule.getLeft(), constrSymbols),
                        this.convertNewTermToOldTerm(prgrm, rule.getRight(), constrSymbols)
                    )
                );
            }
            // Here we have conditions
            else {
                newSet.add(
                    aprove.verification.oldframework.Rewriting.Rule.create(
                        conds,
                        this.convertNewTermToOldTerm(prgrm, rule.getLeft(), constrSymbols),
                        this.convertNewTermToOldTerm(prgrm, rule.getRight(), constrSymbols)
                    )
                );
            }
        }
        return newSet;
    }

    /*
     * Convert new term to old term, is used above
     */
    private aprove.verification.oldframework.Algebra.Terms.AlgebraTerm convertNewTermToOldTerm(
        Program prgrm,
        aprove.verification.dpframework.BasicStructures.TRSTerm newTerm,
        Set<aprove.verification.oldframework.BasicStructures.FunctionSymbol> constrSymbols
    ) {
        // Base case: term is variable
        if (newTerm.isVariable()) {
            // IMPORTANT: EVERY single variable occurring in the rule set has to
            // have a sort
            if (Globals.useAssertions) {
                if (Globals.DEBUG_MICPAR) {
                    if (this.sortCalculator.getVariableSortMap().get(newTerm) == null) {
                        System.out.println(newTerm);
                    }
                }
                assert (this.sortCalculator.getVariableSortMap().get(newTerm) != null);
            }
            String sortName = this.sortCalculator.getVariableSortMap().get(newTerm).getName();
            VariableSymbol varSym = VariableSymbol.create(newTerm.getName(), prgrm.getSort(sortName));
            return aprove.verification.oldframework.Algebra.Terms.AlgebraVariable.create(varSym);
        }
        // Case: Term is not variable
        if (!newTerm.isVariable()) {
            aprove.verification.dpframework.BasicStructures.TRSFunctionApplication funApp =
                ((aprove.verification.dpframework.BasicStructures.TRSFunctionApplication) newTerm);
            // Case: Term is constructor application
            if (constrSymbols.contains(funApp.getRootSymbol())) {
                List<AlgebraTerm> args = new Vector<AlgebraTerm>();
                for (aprove.verification.dpframework.BasicStructures.TRSTerm arg : funApp.getArguments()) {
                    args.add(this.convertNewTermToOldTerm(prgrm, arg, constrSymbols));
                }
                ConstructorSymbol conSym = prgrm.getConstructorSymbol(funApp.getRootSymbol().getName());
                if (Globals.useAssertions) {
                    if (Globals.DEBUG_MICPAR) {
                        if (conSym == null) {
                            System.out.println(funApp);
                        }
                    }
                    assert (conSym != null);
                }
                return aprove.verification.oldframework.Algebra.Terms.ConstructorApp.create(conSym, args);
            }
            // Case: Term is defined function application
            else {
                List<AlgebraTerm> args = new Vector<AlgebraTerm>();
                for (aprove.verification.dpframework.BasicStructures.TRSTerm arg : funApp.getArguments()) {
                    args.add(this.convertNewTermToOldTerm(prgrm, arg, constrSymbols));
                }
                DefFunctionSymbol defFunSym = prgrm.getDefFunctionSymbol(funApp.getRootSymbol().getName());
                if (defFunSym == null) {
                    defFunSym = prgrm.getPredefFunctionSymbol(funApp.getRootSymbol().getName());
                }
                if (Globals.useAssertions) {
                    if (Globals.DEBUG_MICPAR) {
                        if (defFunSym == null) {
                            System.out.println(funApp);
                        }
                    }
                    assert (defFunSym != null);
                }
                return aprove.verification.oldframework.Algebra.Terms.DefFunctionApp.create(defFunSym, args);
            }
        }
        return null;
    }

    /*
     * Compute list of constructor symbols
     */
    private Vector<aprove.verification.oldframework.BasicStructures.FunctionSymbol> computeConstrSymbols(
        ImmutableSet<aprove.verification.dpframework.BasicStructures.Rule> R
    ) {
        Vector<aprove.verification.oldframework.BasicStructures.FunctionSymbol> constrSymbols =
            new Vector<aprove.verification.oldframework.BasicStructures.FunctionSymbol>();
        RuleAnalysis<aprove.verification.dpframework.BasicStructures.Rule> analysis =
            new RuleAnalysis<aprove.verification.dpframework.BasicStructures.Rule>(R, IDPPredefinedMap.EMPTY_MAP);
        ImmutableSet<aprove.verification.oldframework.BasicStructures.FunctionSymbol> allFuns = analysis.getFunctionSymbols();
        ImmutableSet<aprove.verification.oldframework.BasicStructures.FunctionSymbol> defFuns = analysis.getDefinedSymbols();
        // Add new pair to constrSymbols whenever funSym is NOT a
        // defFunctionSymbol
        for (aprove.verification.oldframework.BasicStructures.FunctionSymbol funSym : allFuns) {
            if (!defFuns.contains(funSym)) {
                constrSymbols.add(funSym);
            }
        }
        // quick-fix or is defined symbol
        aprove.verification.oldframework.BasicStructures.FunctionSymbol myOr = this.nameManager.getOrSym();
        constrSymbols.remove(myOr);
        return constrSymbols;
    }

    /*
     * Here we add all the selectors and isa-functions for all constructor
     * symbols
     */
    private Program addPredefinedFunctionsForConstructors(Program prgrm) {
        // For a sort s, we need the symbols for equals for all sorts
        // the constructors of s directly depend on if we want to
        // construct the corresponding equals-rules:
        //
        // equal_List(Cons(x,xs), Cons(y,ys)) -> and(equal_Int(x,y), equal_List(xs,ys))
        //
        // => gather them in advance
        List<Pair<Sort, DefFunctionSymbol>> sortToEqualsSym = this.gatherEqualsSyms(prgrm);
        // Here we add sort and the according constructors to the program
        for (aprove.verification.dpframework.DPProblem.TheoremProver.Sort mysort : this.sortCalculator.getSorts()) {
            //if (mysort.getName().equals("bool")) {
            if (mysort.getName().equals(QDPTheoremProverProcessor.BOOL_SORT)) {
                continue;
            }
            Sort newSort = prgrm.getSort(mysort.getName());
            List<ConstructorSymbol> constrSymbols = newSort.getConstructorSymbols();
            /*
             * Add rules for equals function for the sort
             */
            DefFunctionSymbol equalForNewSort = ProgramInitializer.getValueFromEntryList(sortToEqualsSym, newSort);
            int index = 0;
            for (ConstructorSymbol leftConSym : constrSymbols) {

                List<AlgebraTerm> leftArgs = this.getFreshVariables(leftConSym.getArity(), leftConSym.getArgSorts(), index);
                index += leftConSym.getArity();
                AlgebraTerm innerLeft = ConstructorApp.create(leftConSym, leftArgs);
                for (ConstructorSymbol rightConSym : constrSymbols) {
                    List<AlgebraTerm> rightArgs = this.getFreshVariables(rightConSym.getArity(), rightConSym.getArgSorts(), index);
                    AlgebraTerm innerRight = ConstructorApp.create(rightConSym, rightArgs);
                    List<AlgebraTerm> args = new Vector<AlgebraTerm>();
                    args.add(innerLeft);
                    args.add(innerRight);
                    AlgebraTerm left = DefFunctionApp.create(equalForNewSort, args);
                    // Now calculate right-hand side.
                    AlgebraTerm right;
                    // Check if constructor-symbols are equal, if not return
                    // false
                    if (leftConSym.equals(rightConSym)) {
                        if (leftConSym.isConstant()) {
                            right = ConstructorApp.create(prgrm.getConstructorSymbol(this.nameManager.getTrueName()));
                        }
                        else if (leftConSym.getArity() == 1) {
                            AlgebraTerm innerLeftArg = innerLeft.getArgument(0);
                            AlgebraTerm innerRightArg = innerRight.getArgument(0);
                            Sort lSort = innerLeftArg.getSort();
                            Sort rSort = innerRightArg.getSort();
                            if (Globals.useAssertions) {
                                assert lSort.equals(rSort);
                            }
                            DefFunctionSymbol equalForInnerSort = ProgramInitializer.getValueFromEntryList(sortToEqualsSym, lSort);
                            args = new Vector<AlgebraTerm>();
                            args.add(innerLeftArg);
                            args.add(innerRightArg);
                            right = DefFunctionApp.create(equalForInnerSort, args);
                        }
                        else {
                            // Here the constructor symbol is at least binary,
                            // so we have to split the right side and connect it
                            // with and.
                            //DefFunctionSymbol fand = prgrm.getPredefFunctionSymbol("and");
                            DefFunctionSymbol fand = prgrm.getPredefFunctionSymbol(this.nameManager.getAndName());
                            List<AlgebraTerm> andArgs = new Vector<AlgebraTerm>();
                            for (int argIndex = 0; argIndex < leftConSym.getArity(); argIndex++) {
                                AlgebraTerm innerLeftArg = innerLeft.getArgument(argIndex);
                                AlgebraTerm innerRightArg = innerRight.getArgument(argIndex);
                                Sort lSort = innerLeftArg.getSort();
                                Sort rSort = innerRightArg.getSort();
                                if (Globals.useAssertions) {
                                    assert lSort.equals(rSort);
                                }
                                DefFunctionSymbol equalForInnerSort = ProgramInitializer.getValueFromEntryList(sortToEqualsSym, lSort);
                                args = new Vector<AlgebraTerm>();
                                args.add(innerLeftArg);
                                args.add(innerRightArg);
                                andArgs.add(DefFunctionApp.create(equalForInnerSort, args));
                            }
                            args = new Vector<AlgebraTerm>();
                            args.add(andArgs.remove(0));
                            args.add(andArgs.remove(0));
                            right = DefFunctionApp.create(fand, args);
                            while (!andArgs.isEmpty()) {
                                args = new Vector<AlgebraTerm>();
                                args.add(right);
                                args.add(andArgs.remove(0));
                                right = DefFunctionApp.create(fand, args);
                            }
                        }
                    }
                    else {
                        right = ConstructorApp.create(prgrm.getConstructorSymbol(this.nameManager.getFalseName()));
                    }
                    prgrm.addRule(equalForNewSort, Rule.create(left, right));
                }
                index = 0;
            }
        }
        return prgrm;
    }

    /**
     * @param prgrm - The Program to which we want to add symbols for "equals_s"
     *  for all sorts s; will be modified to know about these defined function
     *  symbols, but will not get any rules for them in this method;
     *  the witness terms will be set in the process
     * @return the mapping from sorts to new defined function symbols
     */
    private List<Pair<Sort, DefFunctionSymbol>> gatherEqualsSyms(Program prgrm) {
        List<Pair<Sort, DefFunctionSymbol>> sortToEqualsSym
            = new ArrayList<Pair<Sort, DefFunctionSymbol>>();
        for (aprove.verification.dpframework.DPProblem.TheoremProver.Sort mysort : this.sortCalculator.getSorts()) {
            if (mysort.getName().equals(QDPTheoremProverProcessor.BOOL_SORT)) {
                continue;
            }
            Sort newSort = prgrm.getSort(mysort.getName());
            TypeContext typeContext = prgrm.getTypeContext();
            DefFunctionSymbol equalForNewSort = DefFunctionSymbol.create(
                    this.nameManager.getEqualsSymbol(mysort.getName()).getName(), 2,
                    newSort, prgrm.getSort(QDPTheoremProverProcessor.BOOL_SORT));
            // by construction
            equalForNewSort.setTermination(true);
            try {
                prgrm.addPredefFunctionSymbol(equalForNewSort);
                prgrm.activatePredefFunctionSymbol(equalForNewSort.getName());
            }
            catch (ProgramException e) {
                e.printStackTrace();
                throw new RuntimeException("Cannot add equal test to program");
            }
            newSort.setEqualOp(equalForNewSort);
            equalForNewSort.setSignatureClass(Symbol.BOOLSIG);
            List<AlgebraTerm> argumentTypes = new Vector<AlgebraTerm>();
            // Call add twice, because equal_sort is binary
            argumentTypes.add(typeContext.getTypeDef(mysort.getName()).getDefTerm());
            argumentTypes.add(typeContext.getTypeDef(mysort.getName()).getDefTerm());
            AlgebraTerm resultType = typeContext.getTypeDef(QDPTheoremProverProcessor.BOOL_SORT).getDefTerm();
            AlgebraTerm equalType = TypeTools.function(argumentTypes, resultType);
            // Allow isa_something only once with this name
            typeContext.setSingleTypeOf(equalForNewSort, TypeTools.autoQuan(equalType));

            List<ConstructorSymbol> constrSymbols = newSort.getConstructorSymbols();
            // Here get default right-hand side for selector, normally take
            // witness term.
            AlgebraTerm defaultRight = null;
            aprove.verification.oldframework.BasicStructures.FunctionSymbol witnessSymbol =
                this.nameManager.getWitnessTerm(mysort.getName());
            String witnessName = witnessSymbol.getName();
            for (ConstructorSymbol conSym : constrSymbols) {
                if (conSym.isConstant() && conSym.getName().equals(witnessName)) {
                    defaultRight = ConstructorApp.create(conSym);
                    break;
                }
            }
            assert defaultRight != null : "Witness for " + mysort + " cannot be found in " + newSort + "!";
            newSort.setWitnessTerm(defaultRight);
            sortToEqualsSym.add(new Pair<Sort, DefFunctionSymbol>(newSort, equalForNewSort));
        }
        return sortToEqualsSym;
    }

    /**
     * Crude simulation of a map for keys that do not have decent hashCode()
     * or compareTo(), but a workable equals().
     *
     * @param <K>
     * @param <V>
     * @param map
     * @param key
     * @return
     */
    private static <K,V> V getValueFromEntryList(List<Pair<K,V>> map, K key) {
        for (Pair<K,V> entry : map) {
            if (entry.x.equals(key)) {
                return entry.y;
            }
        }
        return null;
    }

    /*
     * Return a list of variables of the correct sorts
     */
    private List<AlgebraTerm> getFreshVariables(int arity, List<Sort> list, int start) {
        // get the variables for the inner consym
        List<AlgebraTerm> variables = new Vector<AlgebraTerm>();
        for (int curArg = start; curArg < arity + start; curArg++) {
            String freshName = this.nameManager.getFreshVariable().getName();
            variables.add(aprove.verification.oldframework.Algebra.Terms.AlgebraVariable.create(VariableSymbol.create(
                    /*new String("x" + String.valueOf(curArg))*/freshName,
                    list.get(curArg - start))));
        }
        return variables;
    }

    /*
     * Add constructors to program here
     */
    private Program addConstructorsToProgram(Program prgrm) {
        try {
            // Add bool sort and some basic functions operating on this sort
            //prgrm = Translator.predefine(prgrm);
            prgrm = Translator.predefine(prgrm/*,
                    QDPTheoremProverProcessor.BOOL_SORT,
                    this.nameManager.getTrueName(),
                    this.nameManager.getFalseName(),
                    this.nameManager.getEqualsSymbol(QDPTheoremProverProcessor.BOOL_SORT).getName(),
                    this.nameManager.getAndName(),
                    this.nameManager.getOrName(),
                    this.nameManager.getNotName(),
                    this.nameManager.getIsATrueName(),
                    this.nameManager.getIsAFalseName()*/);

            // laProgramProperties MUST BE null, otherwise conditional
            // evaluation will not be applicable.
            prgrm.laProgramProperties = null;
            // Here add sorts
            Set<Sort> sorts = new LinkedHashSet<Sort>();
            for (aprove.verification.dpframework.DPProblem.TheoremProver.Sort mysort : this.sortCalculator.getSorts()) {
                // Skip creation of bool type
                if (mysort.getName().equals(QDPTheoremProverProcessor.BOOL_SORT)) {
                    continue;
                }
                // Add new type definition
                Sort sort = Sort.create(mysort.getName(), new Vector<ConstructorSymbol>());
                sorts.add(sort);
                TypeDefinition curTypeDef = new TypeDefinition(TypeTools.getTypeCons(sort.getName(), 0));
                // Add type context for sort
                TypeContext typeContext = prgrm.getTypeContext();
                typeContext.addTypeDef(curTypeDef);
                prgrm.addSort(sort);
            }
            // Here add constructors
            for (Sort sort : sorts) {
                ConstructorSymbol consym = null;
                for (
                    aprove.verification.oldframework.BasicStructures.FunctionSymbol constrSymbol :
                        this.sortCalculator.getSortByName(sort.getName()).getConstructors()
                ) {
                    aprove.verification.dpframework.DPProblem.TheoremProver.Sort newSort =
                        this.sortCalculator.getSortByName(sort.getName());
                    if (newSort.getConstructors().contains(constrSymbol)) {
                        // Compute argument sorts!
                        Type tau;
                        List<Sort> argSorts = new Vector<Sort>();
                        // If there are no arguments it's easy
                        if (constrSymbol.getArity() == 0) {
                            AlgebraTerm sortCon = prgrm.getTypeContext().getTypeDef(sort.getName()).getDefTerm();
                            tau = TypeTools.autoQuan(sortCon);
                        }
                        // If there are arguments add the argument sorts
                        // correctly
                        else {
                            List<AlgebraTerm> lot = new Vector<AlgebraTerm>();
                            ImmutableArrayList<aprove.verification.dpframework.DPProblem.TheoremProver.Sort> inputSortList =
                                this.sortCalculator.getFunInputSortMap().get(constrSymbol);
                            Iterator<aprove.verification.dpframework.DPProblem.TheoremProver.Sort> sortIter =
                                inputSortList.iterator();
                            for (int index = 0; index < constrSymbol.getArity(); index++) {
                                String sortName = sortIter.next().getName();
                                AlgebraTerm sortCon = prgrm.getTypeContext().getTypeDef(sortName).getDefTerm();
                                argSorts.add(prgrm.getSort(sortName));
                                lot.add(sortCon);
                            }
                            tau =
                                TypeTools.autoQuan(
                                    TypeTools.function(
                                        lot,
                                        prgrm.getTypeContext().getTypeDef(sort.getName()).getDefTerm()
                                    )
                                );
                        }
                        // Finally create constructor symbol and add it to the
                        // program / sort / type context
                        consym = ConstructorSymbol.create(constrSymbol.getName(), argSorts, sort);
                        prgrm.getTypeContext().getTypeDef(sort.getName()).setSingleTypeOf(consym, tau);
                        sort.addConstructorSymbol(consym);
                        prgrm.addConstructorSymbol(consym);
                    }
                }
            }
        }
        catch (ProgramException e) {
            throw new RuntimeException("Internal error building constructor-symbols for FP/ctrs: " + e.getMessage());
        }
        return prgrm;
    }

}
