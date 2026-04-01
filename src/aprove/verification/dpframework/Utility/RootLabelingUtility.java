package aprove.verification.dpframework.Utility;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 * Some basic functionality for root labeling
 *
 * @author Andreas Kelle-Emden
 */
public class RootLabelingUtility {

    private static final String VAR_PREFIX = "z";

    public static final FunctionSymbol clash;

    static{
        clash = FunctionSymbol.create("CLASH!", 0);
    }

    // Helper functions

    // Get extra clashes from a term
    private static boolean getVarClashes(TRSTerm t, Map<TRSVariable, FunctionSymbol> varMap, Map<FunctionSymbol, FunctionSymbol[]> clashMap) {
        if (t.isVariable()) {
            TRSVariable vt = (TRSVariable)t;
            FunctionSymbol sym = varMap.get(vt);
            if (sym == RootLabelingUtility.clash) {
                return true;
            }
        } else {
            TRSFunctionApplication fat = (TRSFunctionApplication)t;
            FunctionSymbol sym = fat.getRootSymbol();
            int arity = sym.getArity();
            FunctionSymbol[] symArr = clashMap.get(sym);
            for (int i = 0; i < arity; i++) {
                boolean res = RootLabelingUtility.getVarClashes(fat.getArgument(i), varMap, clashMap);
                if (res) {
                    symArr[i] = RootLabelingUtility.clash;
                }
            }
            clashMap.put(sym, symArr);
        }
        return false;
    }

    // Get variable to term assignment sets from a rule
    private static FunctionSymbol getVarAssignments(TRSTerm l, TRSTerm r, Map<TRSVariable, Set<TRSTerm>> varAssMap, Map<FunctionSymbol, FunctionSymbol[]> clashMap) {
        if (l.isVariable()) {
            TRSVariable vl = (TRSVariable)l;
            Set<TRSTerm> termSet = varAssMap.get(vl);
            if (termSet == null) {
                termSet = new LinkedHashSet<TRSTerm>();
            }
            if (r.isVariable()) {
                if (l.equals(r)) {
                    return null;
                }
                // Case 1: l and r are variables
                TRSVariable vr = (TRSVariable)r;
                Set<TRSTerm> termSetr = varAssMap.get(vr);
                if (termSetr == null) {
                    termSetr = new LinkedHashSet<TRSTerm>();
                }
                if (!termSetr.contains(vl)) {
                    termSet.add(vr);
                }
                for (TRSTerm t : termSetr) {
                    if (t.isVariable()) {
                        RootLabelingUtility.getVarAssignments(l, t, varAssMap, clashMap);
                    } else {
                        termSet.add(t);
                    }
                }
                for (TRSTerm t : termSet) {
                    if (t.isVariable()) {
                        RootLabelingUtility.getVarAssignments(t, r, varAssMap, clashMap);
                    } else {
                        termSetr.add(t);
                    }
                }
                varAssMap.put(vr, termSetr);
            } else {
                // Case 2: l is a variable, r is a function application
                for (TRSTerm t : termSet) {
                    RootLabelingUtility.getVarAssignments(t, r, varAssMap, clashMap);
                }
                termSet.add(r);
            }
            varAssMap.put(vl, termSet);
        } else {
            if (r.isVariable()) {
                // Case 3: l is a function application, r is a variable
                TRSVariable vr = (TRSVariable)r;
                Set<TRSTerm> termSet = varAssMap.get(vr);
                if (termSet == null) {
                    termSet = new LinkedHashSet<TRSTerm>();
                }
                for (TRSTerm t : termSet) {
                    RootLabelingUtility.getVarAssignments(l, t, varAssMap, clashMap);
                }
                termSet.add(l);
                varAssMap.put(vr, termSet);
            } else {
                // Case 4: l and r are function applications
                TRSFunctionApplication fal = (TRSFunctionApplication)l;
                TRSFunctionApplication far = (TRSFunctionApplication)r;
                FunctionSymbol syml = fal.getRootSymbol();
                FunctionSymbol symr = far.getRootSymbol();
                if (syml.equals(symr)) {
                    int arity = syml.getArity();
                    FunctionSymbol[] symArr = clashMap.get(syml);
                    for (int i = 0; i < arity; i++) {
                        FunctionSymbol res = RootLabelingUtility.getVarAssignments(fal.getArgument(i), far.getArgument(i), varAssMap, clashMap);
                        if (res != null) {
                            if (symArr[i] != null || res == RootLabelingUtility.clash || !res.equals(symArr[i])) {
                                symArr[i] = RootLabelingUtility.clash;
                            } else {
                                symArr[i] = res;
                            }
                        }
                    }
                    clashMap.put(syml, symArr);
                    return syml;
                } else {
                    return RootLabelingUtility.clash;
                }
            }
        }
        return null;
    }


    // Recursively label a term
//    private static Pair<Term, FunctionSymbol> label(Pair<FunctionSymbol, List<FunctionSymbol>> pair, RootLabelingNameArray nameArray, FunctionSymbol[] symbols, Map<FunctionSymbol, Set<Integer>> labelMap, Variable[] vars, int[] assignment, Term t, Pair<Term, FunctionSymbol> result) {
    private static void label(RootLabelingNameArray nameArray, FunctionSymbol[] symbols, Map<FunctionSymbol, Set<Integer>> labelMap, TRSVariable[] vars, int[] assignment, TRSTerm t, Pair<TRSTerm, FunctionSymbol> result, Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        if (t instanceof TRSVariable) {
            // t is a variable:
            // Return t as is and the assigned function symbol
            // as label for the function application on the next level
            for (int i = 0; i < vars.length; i++) {
                if (((TRSVariable)t).equals(vars[i])) {
                    FunctionSymbol sym = symbols[assignment[i]];
                    result.x = t;
                    result.y = sym;
                    return; // new Pair<Term, FunctionSymbol>(t, sym);
                }
            }
            // This variable is not used for labeling
            result.x = t;
            result.y = null;
            return; // new Pair<Term, FunctionSymbol>(t, null);
            // This line should never be reached!
        } else if (t instanceof TRSFunctionApplication) {
            // t is a function application:
            // recursively collect the labels of the parameters and create
            // a new labelled function application.
            // Return new term and
            // the current symbol for the upper level
            FunctionSymbol sym = ((TRSFunctionApplication)t).getRootSymbol();
            int arity = sym.getArity();
            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(arity);
            Set<Integer> set = labelMap.get(sym);
            Pair<FunctionSymbol, List<FunctionSymbol>> pair = new Pair<FunctionSymbol, List<FunctionSymbol>>(null, new ArrayList<FunctionSymbol>());
            for (int i = 0; i < arity; i++) {
                TRSTerm curArg = ((TRSFunctionApplication)t).getArgument(i);
                //Pair<Term, FunctionSymbol> res = label(pair, nameArray, symbols, labelMap, vars, assignment, curArg, result);
                RootLabelingUtility.label(nameArray, symbols, labelMap, vars, assignment, curArg, result, xmlLabelMap);
                args.add(result.x);
                // Only create a new name, if this symbol gets labeled
                if (set != null && set.contains(i)) {
                    pair.y.add(result.y);
                }
            }
            pair.x = sym;
            FunctionSymbol newSym = nameArray.getLabeled(pair, xmlLabelMap);
            result.x = TRSTerm.createFunctionApplication(newSym, ImmutableCreator.create(args));
            result.y = sym;
            return; // new Pair<Term, FunctionSymbol>(FunctionApplication.createFunctionApplication(newSym, ImmutableCreator.create(args)), sym);
        }
        // This should never happen!
        return; // null;
    }


    // Given a label map and a rule, decide which variables must be used
    // for labeling
    private static void checkVariablesRec(TRSFunctionApplication fa, Set<TRSVariable> varSet, Map<FunctionSymbol, Set<Integer>> labelMap) {
        FunctionSymbol sym = fa.getRootSymbol();
        int arity = sym.getArity();
        for (int i = 0; i < arity; i++) {
            // Check subterms
            TRSTerm t = fa.getArgument(i);
            if (t instanceof TRSVariable) {
                Set<Integer> set = labelMap.get(sym);
                if (set != null && set.contains(i)) {
                    // t is a variable and the current function symbol
                    // gets labeled - we have to consider t
                    varSet.add((TRSVariable)t);
                }
            } else {
                RootLabelingUtility.checkVariablesRec((TRSFunctionApplication)t, varSet, labelMap);
            }
        }
    }
    private static TRSVariable[] checkVariables(Rule rule, Map<FunctionSymbol, Set<Integer>> labelMap) {
        Set<TRSVariable> varSet = new LinkedHashSet<TRSVariable>();
        // Check left term
        TRSFunctionApplication l = rule.getLeft();
        RootLabelingUtility.checkVariablesRec(l, varSet, labelMap);
        // Check right term, if it is a function application
        TRSTerm r = rule.getRight();
        if (r instanceof TRSFunctionApplication) {
            RootLabelingUtility.checkVariablesRec((TRSFunctionApplication)r, varSet, labelMap);
        }
        // Create array
        TRSVariable[] varArr = new TRSVariable[varSet.size()];
        int i = 0;
        for (TRSVariable v: varSet) {
            varArr[i] = v;
            i++;
        }

        return varArr;
    }

    // Public functions


    /**
     * Does the root-labeling on a given set of rules R.
     *
     *  @param rules - Rules to be labelled
     *  @param labelSyms - With these symbols function symbols get labelled
     *  @param labelMap - Which function symbols get labeled and which parameters should be respected?
     *  @param aborter - Abortion
     *  @return the new set of labelled rules
     */
    public static Set<Rule> labelRules(Set<Rule> rules, Set<FunctionSymbol> labelSyms, Map<FunctionSymbol, Set<Integer>> labelMap, Abortion aborter, Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) throws AbortionException {

        Set<Rule> newRules = new LinkedHashSet<Rule>();

        RootLabelingNameArray nameArray = RootLabelingNameArray.create();

        // Create function symbol array
        int numsyms = labelSyms.size();
        FunctionSymbol[] symbols = new FunctionSymbol[numsyms];
        int i = 0;
        for (FunctionSymbol sym : labelSyms) {
            symbols[i] = sym;
            i++;
        }

        for (Rule rule: rules) {
            RootLabelingUtility.labelOneRule(labelMap, aborter, xmlLabelMap, newRules, nameArray,
                    numsyms, symbols, rule);
        }
        return newRules;
    }

    private static void labelOneRule(
            Map<FunctionSymbol, Set<Integer>> labelMap,
            Abortion aborter,
            Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap,
            Set<Rule> newRules, RootLabelingNameArray nameArray,
            int numsyms,
            FunctionSymbol[] symbols, Rule rule) throws AbortionException {
        Pair<TRSTerm, FunctionSymbol> result = new Pair<TRSTerm, FunctionSymbol>(null, null);
        int i;
        // Create variable array for current rule
        TRSVariable[] vars = RootLabelingUtility.checkVariables(rule, labelMap);
        int numvars = vars.length;

        boolean stopLoop = false;
        // We need to create |symbols|^|vars| different new rules here
        int[] loopList = new int[numvars];
        for (i = 0; i < numvars; i++) {
            loopList[i] = 0;
        }
        while (!stopLoop) {
            aborter.checkAbortion();
            // Label the rule
            //Pair<Term, FunctionSymbol> pairL = label(pair, nameArray, symbols, labelMap, vars, loopList, rule.getLeft(), result);
            //Pair<Term, FunctionSymbol> pairR = label(pair, nameArray, symbols, labelMap, vars, loopList, rule.getRight(), result);
            RootLabelingUtility.label(nameArray, symbols, labelMap, vars, loopList, rule.getLeft(), result, xmlLabelMap);
            TRSTerm tl = result.x;
            RootLabelingUtility.label(nameArray, symbols, labelMap, vars, loopList, rule.getRight(), result, xmlLabelMap);
            newRules.add(Rule.create((TRSFunctionApplication)tl, result.x));


            // Go to next variable assignment
            if (numvars == 0) {
                stopLoop = true;
            }
            for (i = numvars-1; i >= 0; i--) {
                loopList[i]++;
                if (loopList[i] < numsyms) {
                    break;
                }
                loopList[i] = 0;
                if (i == 0)
                 {
                    stopLoop = true;
                    // all possible variable assignments have been added
                }
            }
        }
    }


    public static Set<Rule> labelRules(Set<Rule> rules, Set<FunctionSymbol> labelSyms, Map<FunctionSymbol, Set<Integer>> labelMap, Abortion aborter, int threads, Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) throws AbortionException {
        if (threads <= 1) {
            // Only one thread or undefined max thread number - do it the old way
            return RootLabelingUtility.labelRules(rules, labelSyms, labelMap, aborter, xmlLabelMap);
        }

        // Do it the parallel way
        RootLabelingNameArray nameArray = RootLabelingNameArray.create();

        // Create function symbol array
        int numsyms = labelSyms.size();
        FunctionSymbol[] symbols = new FunctionSymbol[numsyms];
        int i = 0;
        for (FunctionSymbol sym : labelSyms) {
            symbols[i] = sym;
            i++;
        }

        List<LabelWorker> workList = new LinkedList<LabelWorker>();

        for (Rule rule: rules) {
            workList.add(new LabelWorker(rule, labelMap, nameArray, symbols, labelSyms, xmlLabelMap));
        }
        MultithreadedExecutor.execute(workList, aborter);
        aborter.checkAbortion();

        Set<Rule> newRules = new LinkedHashSet<Rule>();
        for(LabelWorker worker: workList) {
            if (worker.resultingRules == null) {
                throw new RuntimeException("RootLabeling worker failed!");
            }
            newRules.addAll(worker.resultingRules);
        }

        return newRules;
    }


    /**
     * Given a set of rules R, this method creates a new set of rules R' where
     * every rule is root-preserving. Therefore it adds the flat contexts for
     * every root-altering rule to R'.
     *
     *  @param rules - Set of rules R
     *  @param symbols - function symbols to be used for flat contexts. If null, every function symbol in R will be used
     *  @param aborter - Abortion
     *  @param flatContexts - will be filled with the generated flat contexts
     *   if non-null
     *  @param fng - will be used to generate fresh variable names for the contexts;
     *   it is the responsibility of the caller to ensure that fng never generates
     *   any name that is the name of a variable in a rule
     *  @return the new set of root-preserving rules R'
     */
    public static Set<Rule> flatContext(Set<Rule> rules, Set<FunctionSymbol> symbols, Abortion aborter, Collection<Context> flatContexts,
            FreshNameGenerator fng) throws AbortionException {
        LinkedHashSet<Rule> newRules = new LinkedHashSet<Rule>(rules);
        if (symbols == null) {
            symbols = new LinkedHashSet<FunctionSymbol>();
            for (Rule rule : rules) {
                symbols.addAll(rule.getFunctionSymbols());
            }
        }
        for (Rule rule: rules) {
            TRSFunctionApplication l = rule.getLeft();
            TRSTerm r = rule.getRight();
            boolean nonRootPreserving = false;
            boolean addedSymbols = false;
            // A rule l -> r is non root-preserving if r is a variable
            // or root(l) != root(r)
            if (r instanceof TRSFunctionApplication) {
                if (!l.getRootSymbol().equals(((TRSFunctionApplication)r).getRootSymbol())) {
                    nonRootPreserving = true;
                }
            } else {
                nonRootPreserving = true;
            }
            if (nonRootPreserving) {
                // Remove the rule from Rules
                newRules.remove(rule);
                // Create flat contexts
                for (FunctionSymbol sym : symbols) {
                    aborter.checkAbortion();
                    int len = sym.getArity();
                    // Create new variables for the flat context
                    TRSVariable[] newVars = new TRSVariable[len];
                    TRSTerm[] argsL = new TRSTerm[len];
                    TRSTerm[] argsR = new TRSTerm[len];
                    for (int i = 0; i < len; i++) {
                        String freshName = fng.getFreshName(RootLabelingUtility.VAR_PREFIX + i, true);
                        argsL[i] = argsR[i] = newVars[i] = TRSTerm.createVariable(freshName);
                    }
                    // Create flat contexts
                    for (int i = 0; i < len; i++) {
                        argsL[i] = rule.getLeft();
                        argsR[i] = rule.getRight();
                        TRSFunctionApplication newL = TRSTerm.createFunctionApplication(sym, argsL);
                        if (!addedSymbols && flatContexts!=null) {
                            // just add the Context ONCE under the condition
                            // that there actually has been some flattening
                            flatContexts.add(Context.create(newL, Position.create(new int[] {i})));
                        }
                        TRSFunctionApplication newR = TRSTerm.createFunctionApplication(sym, argsR);
                        newRules.add(Rule.create(newL, newR));
                        argsL[i] = newVars[i];
                        argsR[i] = newVars[i];
                    }
                }
                addedSymbols = true;
            }
        }
        return newRules;
    }

    /**
     * Build block(R) for a given set of rules R and a given function symbol DELTA
     *
     *  @param rules - Set of rules R
     *  @param delta - new function symbol with arity 1
     *  @param aborter - Abortion
     *  @return block(R) or null, if some error occured
     */
    public static Set<Rule> block(Set<Rule> rules, FunctionSymbol delta, Abortion aborter) throws AbortionException {
        // delta must have arity 1!
        if (delta.getArity() != 1) {
            return null;
        }

        Set<Rule> newRules = new LinkedHashSet<Rule>();

        // built block(.) for every rule
        for (Rule rule : rules) {
            aborter.checkAbortion();
            // block the left hand side
            TRSFunctionApplication left = rule.getLeft();
            int leftArity = left.getRootSymbol().getArity();
            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(leftArity);
            for (int i = 0; i < leftArity; i++) {
                // For every argument arg...
                TRSTerm oldArg = left.getArgument(i);
                // ...create delta(arg)...
                ArrayList<TRSTerm> newArgArgs = new ArrayList<TRSTerm>(1);
                newArgArgs.add(oldArg);
                TRSFunctionApplication newArg = TRSTerm.createFunctionApplication(delta, ImmutableCreator.create(newArgArgs));
                // ...and replace arg by delta(arg)
                args.add(newArg);
            }
            left = TRSTerm.createFunctionApplication(left.getRootSymbol(), ImmutableCreator.create(args));
            // and now the same for the right hand side, if applicable
            TRSTerm right = rule.getRight();
            if (right instanceof TRSFunctionApplication) {
                int rightArity = ((TRSFunctionApplication)right).getRootSymbol().getArity();
                args = new ArrayList<TRSTerm>(rightArity);
                for (int i = 0; i < rightArity; i++) {
                    TRSTerm oldArg = ((TRSFunctionApplication)right).getArgument(i);
                    ArrayList<TRSTerm> newArgArgs = new ArrayList<TRSTerm>(1);
                    newArgArgs.add(oldArg);
                    TRSFunctionApplication newArg = TRSTerm.createFunctionApplication(delta, ImmutableCreator.create(newArgArgs));
                    args.add(newArg);
                }
                right = TRSTerm.createFunctionApplication(((TRSFunctionApplication)right).getRootSymbol(), ImmutableCreator.create(args));
            }
            Rule newRule = Rule.create(left, right);
            newRules.add(newRule);
        }
        return newRules;
    }



    public static void collectClashes(TRSFunctionApplication l, TRSTerm r, Map<FunctionSymbol, FunctionSymbol[]> clashMap) {
        Map<TRSVariable, Set<TRSTerm>> varAssMap = new LinkedHashMap<TRSVariable, Set<TRSTerm>>();
        // Get all variable assignments
        RootLabelingUtility.getVarAssignments(l, r, varAssMap, clashMap);

        // Create variable map from assignment map
        Map<TRSVariable, FunctionSymbol> varMap = new LinkedHashMap<TRSVariable, FunctionSymbol>();
        for (Map.Entry<TRSVariable, Set<TRSTerm>> entry : varAssMap.entrySet()) {
            TRSVariable v = entry.getKey();
            Set<TRSTerm> termSet = entry.getValue();
            if (termSet == null) {
                continue;
            }
            FunctionSymbol sym = null;
            for (TRSTerm t : termSet) {
                if (t.isVariable()) {
                    continue;
                }
                FunctionSymbol thisSym = ((TRSFunctionApplication)t).getRootSymbol();
                if (sym == null) {
                    sym = thisSym;
                } else {
                    if (thisSym == RootLabelingUtility.clash) {
                        sym = RootLabelingUtility.clash;
                        break;
                    } else {
                        if (!sym.equals(thisSym)) {
                            sym = RootLabelingUtility.clash;
                            break;
                        }
                    }
                }
            }
            varMap.put(v, sym);
        }

        // and now for the clashes
        RootLabelingUtility.getVarClashes(l, varMap, clashMap);
        RootLabelingUtility.getVarClashes(r, varMap, clashMap);
    }



    // Support for parallel root labeling

    private static Rule getNextRule(Iterator<Rule> ruleIterator) {
        Rule res = null;
        synchronized (ruleIterator) {
            if (ruleIterator.hasNext()) {
                res = ruleIterator.next();
            }
        }
        return res;
    }

    private static void storeRules(Set<Rule> rules, Set<Rule> storeInto) {
        synchronized (storeInto) {
            storeInto.addAll(rules);
        }
    }

    private static class LabelWorker implements AbortableRunnable {

        private Rule rule;
        private Set<Rule>      resultingRules = null;
        private Map<FunctionSymbol, Set<Integer>> labelMap;
        private RootLabelingNameArray             nameArray;
        private FunctionSymbol[]    symbols;
        private Set<FunctionSymbol> labelSyms;
        private Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap;

        public LabelWorker (Rule rule, Map<FunctionSymbol, Set<Integer>> labelMap, RootLabelingNameArray nameArray,
                FunctionSymbol[] symbols, Set<FunctionSymbol> labelSyms, Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
            this.rule = rule;
            this.labelMap     = labelMap;
            this.nameArray    = nameArray;
            this.symbols      = symbols;
            this.labelSyms    = labelSyms;
            this.xmlLabelMap  = xmlLabelMap;
        }

        @Override
        public WorkStatus execute(Abortion aborter) throws AbortionException {
            int numsyms = this.labelSyms.size();
            Set<Rule> result = new LinkedHashSet<Rule>();
            RootLabelingUtility.labelOneRule(this.labelMap, aborter, this.xmlLabelMap, result, this.nameArray, numsyms, this.symbols, this.rule);
            this.resultingRules = result;
            return WorkStatus.CONTINUE;
        }

    }

}
