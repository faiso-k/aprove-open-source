package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BooleanSemanticLabelling.*;
import aprove.verification.oldframework.BooleanSemanticLabelling.BSLTermInterpretor.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A labeller that uses the Boolean Tuple Semantic Labelling Term Interpretor
 * which knows which functions to use for evaluation.
 * @author cotto
  */
public class BooleanTupleLabeller implements Labeller {

    /**
     * The Boolean Tuple Semantic Labelling Term Interpretor that knows which
     * functions to use.
     */
    private final BSLTermInterpretor bslti;

    /**
     * The solution found using the SAT search.
     */
    private final int[] solution;

    /**
     * The size of the carrier set (2^dim).
     */
    private final int carrierSetSize;

    /**
     * The (dummy) function representation.
     */
    private final FunctionRepresentation representation;

    /**
     * Remember what the original function symbol looks like for each labelled
     * symbol.
     */
    private final Map<FunctionSymbol, FunctionSymbol> labelToOriginMap;

    /**
     * Cache the labelled terms (and values) for each term.
     */
    private Map<TRSTerm, Pair<ElementValue, TRSTerm>> labelCache;

    /**
     * Cache the value for each term.
     */
    private Map<TRSTerm, BooleanTupleElementValue> cache;

    /**
     * Remember all function symbols seen.
     */
    private final Set<FunctionSymbol> functionSymbols;

    /**
     * The dimension used for the boolean tuple element values.
     */
    private final int dimension;

    /**
     * Create a labeller that uses the solution found by the SAT solver and
     * prepared by the BSLTI.
     * @param representationParam Some dummy function representation.
     * @param bsltiParam The BSLTI that prepared the formula.
     * @param solutionParam The solution for the formula.
     */
    public BooleanTupleLabeller(final FunctionRepresentation representationParam, final BSLTermInterpretor bsltiParam,
            final int[] solutionParam) {
        this.carrierSetSize = representationParam.getCarrierSetSize();
        this.dimension = (int) (Math.log(this.carrierSetSize) / Math.log(2));
        this.representation = representationParam;
        this.labelToOriginMap = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        this.solution = solutionParam;
        this.bslti = bsltiParam;
        this.functionSymbols = new LinkedHashSet<FunctionSymbol>();
    }

    /**
     * @return the map that provides the original unlabelled function symbol for
     * each labelled function symbol.
     */
    @Override
    public Map<FunctionSymbol, FunctionSymbol> getLabelToOriginMap() {
        return this.labelToOriginMap;
    }

    /**
     * Label the given rule and add the results to "addHere".
     * @param rule the rule to label.
     * @param addHere the set where the results are collected.
     */
    @Override
    public void addLabeled(final Rule rule,
        final Collection<Rule> addHere,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        this.functionSymbols.addAll(rule.getFunctionSymbols());
        final Set<TRSVariable> variables = rule.getVariables();
        final int variableCount = variables.size();

        final Pair<ElementValue, TRSTerm> result = new Pair<ElementValue, TRSTerm>(null, null);

        final ElementVectorIterator valueIter = new ElementVectorIterator(variableCount, this.carrierSetSize);
        while (valueIter.hasNext()) {
            this.labelCache = new LinkedHashMap<TRSTerm, Pair<ElementValue, TRSTerm>>();
            this.cache = new LinkedHashMap<TRSTerm, BooleanTupleElementValue>();

            final Iterator<TRSVariable> variableIter = variables.iterator();
            final Map<TRSVariable, ElementValue> varMap = new HashMap<TRSVariable, ElementValue>(variableCount);
            for (final int value : valueIter.next()) {
                varMap.put(variableIter.next(), this.representation.getElementValue(value));
            }
            final Map<TRSVariable, List<Boolean>> boolVarMap = new LinkedHashMap<TRSVariable, List<Boolean>>();
            final Set<TRSVariable> vars = rule.getVariables();
            for (final TRSVariable var : vars) {
                final BooleanTupleElementValue ev = (BooleanTupleElementValue) varMap.get(var);
                final List<Boolean> bools = ev.getBools();
                boolVarMap.put(var, bools);
            }

            this.generateLabeled(rule.getLeft(), boolVarMap, result);
            final TRSFunctionApplication lLeft = (TRSFunctionApplication) result.y;

            this.generateLabeled(rule.getRight(), boolVarMap, result);
            addHere.add(Rule.create(lLeft, result.y));
        }
    }

    /**
     * Label the given rule and add the results to "addHere". For head symbols
     * also add the labelled rules where the label of the right side's root
     * symbol is decreased. F_2 -> F_2 | F_1 | F_0.
     * @param rule the rule to label.
     * @param addHere the set where all labelled rules are collected.
     * @param headSyms all head symbols.
     */
    @Override
    public void addQuasiLabeledPairs(final Rule rule,
        final Collection<Rule> addHere,
        final Set<FunctionSymbol> headSyms,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        this.functionSymbols.addAll(rule.getFunctionSymbols());
        final TRSTerm rhs = rule.getRight();
        if (rhs.isVariable()) {
            this.addLabeled(rule, addHere, xmlLabelMap);
        } else {
            final TRSFunctionApplication fr = (TRSFunctionApplication) rhs;
            final FunctionSymbol f = fr.getRootSymbol();
            if (headSyms.contains(f)) {
                // okay we have to build pairs lab(l) -> t where t is like
                // lab(r) but the label for the outermost f is decreased in all
                // possible ways
                final Set<TRSVariable> variables = rule.getVariables();
                final int variableCount = variables.size();

                final Pair<ElementValue, TRSTerm> result = new Pair<ElementValue, TRSTerm>(null, null);

                final ElementVectorIterator valueIter = new ElementVectorIterator(variableCount, this.carrierSetSize);
                while (valueIter.hasNext()) {
                    final Iterator<TRSVariable> variableIter = variables.iterator();
                    final Map<TRSVariable, ElementValue> varMap = new HashMap<TRSVariable, ElementValue>(variableCount);
                    for (final int value : valueIter.next()) {
                        varMap.put(variableIter.next(), this.representation.getElementValue(value));
                    }

                    final Map<TRSVariable, List<Boolean>> boolVarMap = new LinkedHashMap<TRSVariable, List<Boolean>>();
                    final Set<TRSVariable> vars = rule.getVariables();
                    for (final TRSVariable var : vars) {
                        final BooleanTupleElementValue ev = (BooleanTupleElementValue) varMap.get(var);
                        final List<Boolean> bools = ev.getBools();
                        boolVarMap.put(var, bools);
                    }
                    this.labelCache = new LinkedHashMap<TRSTerm, Pair<ElementValue, TRSTerm>>();
                    this.cache = new LinkedHashMap<TRSTerm, BooleanTupleElementValue>();
                    this.generateLabeled(rule.getLeft(), boolVarMap, result);
                    final TRSFunctionApplication lLeft = (TRSFunctionApplication) result.y;

                    final List<? extends TRSTerm> args = fr.getArguments();
                    final ArrayList<TRSTerm> labArgs = new ArrayList<TRSTerm>(args.size());
                    final List<ElementValue> interArgs = new ArrayList<ElementValue>(args.size());
                    for (final TRSTerm arg : args) {
                        this.generateLabeled(arg, boolVarMap, result);
                        labArgs.add(result.y);
                        interArgs.add(result.x);
                    }

                    final ImmutableArrayList<? extends TRSTerm> finalArgs = ImmutableCreator.create(labArgs);

                    // now iterate over all smaller or equal elements of lab(f)
                    final Iterator<List<ElementValue>> smallerI = this.representation.getSmallerElements(interArgs);
                    while (smallerI.hasNext()) {
                        final List<ElementValue> nextSmaller = smallerI.next();
                        final FunctionSymbol smallerF = this.generateLabeledSymbol(f, nextSmaller);
                        addHere.add(Rule.create(lLeft, TRSTerm.createFunctionApplication(smallerF, finalArgs)));
                    }
                }
            } else {
                this.addLabeled(rule, addHere, xmlLabelMap);
            }
        }
    }

    /**
     * Not needed.
     * @param term not used.
     * @param addHere not used.
     */
    @Override
    public void addLabeled(final TRSFunctionApplication term,
        final Set<TRSFunctionApplication> addHere,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        assert (false) : "Why is this needed?";
        return;
    }

    /**
     * Label the given term where the variables have some given value. Store the
     * result, consisting of the term's value and the labelled term, into
     * "result".
     * @param t The term to label.
     * @param varMap Information about the variables' values.
     * @param result The result.
     */
    private void generateLabeled(final TRSTerm t,
        final Map<TRSVariable, List<Boolean>> varMap,
        final Pair<ElementValue, TRSTerm> result) {
        if (t.isVariable()) {
            result.x = new BooleanTupleElementValue(varMap.get(t), this.carrierSetSize);
            result.y = t;
        } else {
            if (this.labelCache.containsKey(t)) {
                result.x = this.labelCache.get(t).x;
                result.y = this.labelCache.get(t).y;
                return;
            }
            final TRSFunctionApplication ft = (TRSFunctionApplication) t;
            final FunctionSymbol f = ft.getRootSymbol();

            // label all arguments
            final List<? extends TRSTerm> args = ft.getArguments();
            final List<ElementValue> interList = new ArrayList<ElementValue>(args.size());
            final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            for (final TRSTerm arg : args) {
                final Pair<ElementValue, TRSTerm> argResult = new Pair<ElementValue, TRSTerm>(null, null);
                this.generateLabeled(arg, varMap, argResult);
                interList.add(argResult.x);
                newArgs.add(argResult.y);
            }

            result.x = this.evaluate(t, varMap);

            final FunctionSymbol labelF = this.generateLabeledSymbol(f, interList);
            result.y = TRSTerm.createFunctionApplication(labelF, ImmutableCreator.create(newArgs));
            this.labelCache.put(t, result);
        }
    }

    /**
     * @return the value of the given term.
     * @param t Find out the value of this term.
     * @param varMap Information about the variables' values.
     */
    private ElementValue evaluate(final TRSTerm t, final Map<TRSVariable, List<Boolean>> varMap) {
        if (t.isVariable()) {
            return new BooleanTupleElementValue(varMap.get(t), this.carrierSetSize);
        } else {
            if (this.cache.containsKey(t)) {
                return (this.cache.get(t));
            }
            final Formula<None>[] formula = this.bslti.getValue(t, varMap);
            final Boolean[] result = new Boolean[formula.length];
            for (int i = 0; i < formula.length; i++) {
                if (formula[i] != null) {
                    result[i] = this.inSolution(formula[i]);
                } else {
                    // tuple symbols
                    result[i] = false;
                }
            }
            final BooleanTupleElementValue ev = new BooleanTupleElementValue(result, this.carrierSetSize);
            this.cache.put(t, ev);
            return ev;
        }
    }

    /**
     * Find out if the given formula is satisfied in the solution.
     * @param formula a formula that is part of the big formula used to generate
     * the solution.
     * @return true iff the given formula is satisfied in the solution.
     */
    private Boolean inSolution(final Formula<None> formula) {
        assert (this.solution != null && formula != null);
        if (formula.isConstant()) {
            final Constant<None> constant = (Constant<None>) formula;
            return constant.getValue();
        } else {
            final int id = formula.getId();
            return this.solution[id - 1] == id;
        }
    }

    /**
     * Attach a label to the function symbol based on the provided values.
     * The function used to generate the label is the identity.
     * @param f The function symbol to label.
     * @param interList The values of the arguments.
     * @return the labelled function symbol.
     */
    private FunctionSymbol generateLabeledSymbol(final FunctionSymbol f, final List<ElementValue> interList) {
        String s = "";
        boolean first = true;
        for (final ElementValue value : interList) {
            if (first) {
                first = false;
            } else {
                s += "-";
            }
            s += value.toString();
        }
        // as we currently have an injective mapping, we just create the
        // labelled symbol and do not check on clashes.
        final FunctionSymbol labelF = FunctionSymbol.create(f.getName() + "." + s, f.getArity());
        this.labelToOriginMap.put(labelF, f);
        return labelF;
    }

    /**
     * Remove the labels.
     * @param rule the rule to unlabel.
     * @return The unlabelled rule.
     */
    @Override
    public Rule unlabel(final Rule rule) {
        return Rule.create((TRSFunctionApplication) this.unlabel(rule.getLeft()), this.unlabel(rule.getRight()));
    }

    /**
     * Remove the labels.
     * @param t The term to unlabel.
     * @return The unlabelled term.
     */
    public TRSTerm unlabel(final TRSTerm t) {
        if (t.isVariable()) {
            return t;
        } else {
            final TRSFunctionApplication ft = (TRSFunctionApplication) t;
            final FunctionSymbol f = this.labelToOriginMap.get(ft.getRootSymbol());
            final List<? extends TRSTerm> args = ft.getArguments();
            final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            for (final TRSTerm arg : args) {
                newArgs.add(this.unlabel(arg));
            }
            return TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
        }
    }

    /**
     * Not needed.
     * @return null
     */
    @Override
    public Set<Rule> getDecreasingRules(final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        assert (false);
        return null;
    }

    /**
     * For every given function symbol f produce rules
     * f_i(x, y, z) -> f_j(x, y, z)
     * where i,j are labels and i > j.
     * @return all rules with smaller label for each fs.
     * @param fs the set of function symbols that should be used.
     */
    @Override
    public Set<Rule> getDecreasingRules(final Collection<FunctionSymbol> fs,
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        final Set<Rule> result = new LinkedHashSet<Rule>(fs.size());
        final Map<Integer, ImmutableArrayList<TRSTerm>> arityToXs = new HashMap<Integer, ImmutableArrayList<TRSTerm>>();
        for (final FunctionSymbol f : fs) {
            final int n = f.getArity();
            if (n != 0) {
                final Integer arity = n;
                ImmutableArrayList<TRSTerm> xs = arityToXs.get(arity);
                if (xs == null) {
                    final ArrayList<TRSTerm> ys = new ArrayList<TRSTerm>(arity);
                    for (int i = 0; i < n; i++) {
                        ys.add(TRSTerm.createVariable("x" + i));
                    }
                    xs = ImmutableCreator.create(ys);
                    arityToXs.put(arity, xs);
                }
                for (final ElementPair p : this.representation.getDecrElementPairs(n)) {
                    final FunctionSymbol lF = this.generateLabeledSymbol(f, p.getLeft());
                    final FunctionSymbol rF = this.generateLabeledSymbol(f, p.getRight());
                    final TRSFunctionApplication l = TRSTerm.createFunctionApplication(lF, xs);
                    final TRSFunctionApplication r = TRSTerm.createFunctionApplication(rF, xs);
                    result.add(Rule.create(l, r));
                }
            }
        }
        return result;
    }

    /**
     * @return a string that gives information about the functions used to
     * interpret the function symbols.
     * @param o the export util used to generate the result string.
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append("Interpretation over boolean tuples of dimension " + this.dimension + " (carrier set of size "
            + this.carrierSetSize + ").");
        sb.append(o.newline());
        for (final FunctionSymbol fs : this.functionSymbols) {
            final List<Set<Integer>> used = new ArrayList<Set<Integer>>(this.dimension);
            final List<Set<Integer>> negated = new ArrayList<Set<Integer>>(this.dimension);
            final List<BSLTermInterpretor.FunctionPool> usedFunctions =
                new ArrayList<BSLTermInterpretor.FunctionPool>(this.dimension);
            for (int i = 0; i < this.dimension; i++) {
                for (final BSLTermInterpretor.FunctionPool func : BSLTermInterpretor.FunctionPool.values()) {
                    final Formula<None> funcFormula = this.bslti.getFunction(fs, i, func);
                    if (this.inSolution(funcFormula)) {
                        usedFunctions.add(i, func);
                        break; // only one function will be used
                    }
                }
                used.add(i, new LinkedHashSet<Integer>());
                negated.add(i, new LinkedHashSet<Integer>());
                for (int j = 0; j < fs.getArity(); j++) {
                    final Formula<None> filterFormula = this.bslti.getFilter(fs, i, j);
                    if (filterFormula != null && this.inSolution(filterFormula)) {
                        used.get(i).add(j);
                    }
                    final Formula<None> notFormula = this.bslti.getNot(fs, i, j);
                    if (notFormula != null && this.inSolution(notFormula)) {
                        negated.get(i).add(j);
                    }
                }
            }
            sb.append("VAL[");
            sb.append(fs.export(o));
            if (fs.getArity() > 0) {
                sb.append("(");
            }
            int counter = 0;
            boolean firstDim = true;
            for (int i = 0; i < this.dimension; i++) {
                if (!firstDim && fs.getArity() > 0) {
                    sb.append(", ");
                }
                firstDim = false;
                boolean first = true;
                for (int j = 0; j < fs.getArity(); j++) {
                    if (!first) {
                        sb.append(", ");
                    }
                    first = false;
                    sb.append("x_");
                    sb.append(counter);
                    counter++;
                }
            }
            if (fs.getArity() > 0) {
                sb.append(")");
            }
            sb.append("]");
            sb.append(" = ");
            sb.append("[");
            firstDim = true;
            for (int i = 0; i < this.dimension; i++) {
                if (!firstDim) {
                    sb.append(", ");
                }
                firstDim = false;
                counter = 0;
                final FunctionPool function = usedFunctions.get(i);
                final StringBuilder arguments = new StringBuilder();
                boolean firstArgument = true;
                for (int j = 0; j < fs.getArity(); j++) {
                    for (int k = 0; k < this.dimension; k++) {
                        if (used.get(k).contains(j)) {
                            if (!firstArgument) {
                                arguments.append(", ");
                            }
                            firstArgument = false;
                            if (negated.get(k).contains(j)) {
                                arguments.append("-");
                            }
                            arguments.append("x_");
                            arguments.append(counter);
                        }
                        counter++;
                    }
                }
                if (arguments.length() > 0) {
                    arguments.insert(0, "(");
                    arguments.append(")");
                    sb.append(function);
                    sb.append(arguments);
                } else {
                    if (function.equals(FunctionPool.AND)) {
                        sb.append("1");
                    } else if (function.equals(FunctionPool.OR)) {
                        sb.append("0");
                    } else if (function.equals(FunctionPool.XOR)) {
                        sb.append("0");
                    } else {
                        assert (false) : "Please implement.";
                        sb.append(function);
                    }
                }
            }
            sb.append("]");
            sb.append(o.newline());
        }
        return sb.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        throw new UnsupportedOperationException();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<FunctionSymbol> labelFS(final FunctionSymbol funcSym,
        final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap) {
        assert (false);
        return null;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData, final int carrierSize, final boolean quasi)
    {
        return CPFTag.notYetImplemented(doc, this);
    }

    @Override
    public String isCPFSupported() {
        return this.getClass().getCanonicalName();
    }

}
