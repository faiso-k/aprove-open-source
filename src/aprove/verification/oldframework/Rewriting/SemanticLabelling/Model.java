package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.solver.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BooleanSemanticLabelling.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The model of a TRS, assigning functions over a carrier set to
 * function symbols of the term rewriting system, which is necessary
 * for Semantic Labelling, is abstracted by this class. It provides
 * functions to access and set the function-to-symbol-mapping as well
 * as automatically extend existing models in respect to new rules and
 * all the required functionality like verifying the model.
 *
 * @author Christian Hang
 */
public final class Model {

    /**
     * Static logging device to which all debug messages will be
     * fowarded.
     */
    protected static Logger logger =
        Logger.getLogger("aprove.verification.oldframework.Rewriting.SemanticLabelling.Model");

    /**
     * When interpreting over Boolean Tuples some changes are needed, so
     * remember that.
     */
    private boolean useBooleanTuples;

    /**
     * The (SAT) engine that will be used to find models using Boolean Tuples.
     */
    private Engine engine;

    /**
     * Indicating the number of elements in the carrier set. The
     * actual elements of the carrier set are modelled and provided by
     * the implementation of the {@link FunctionRepresentation
     * FunctionRepresentation} used.
     */
    private final int carrierSetSize;

    /**
     *  A mapping between {@link
     *  aprove.verification.oldframework.Syntax.SyntacticFunctionSymbol FunctionSymbol} and
     *  {@link FunctionRepresentation FunctionRepresentation},
     *  containing the actual model.
     */
    private Map<FunctionSymbol, FunctionRepresentation> model;

    /**
     * The implementation of the <code>FunctionRepresentation</code>
     * used is stored in this attribute to access the methods needed
     * to manipulate the functions and elements.
     */
    private FunctionRepresentation defaultRepresentation;

    /**
     * YES, if we have a quasi model (and not a model).
     * NO, if we cannot have a quasi model as we have weakly monotonic functions
     * MAYBE, if we are unsure.
     */
    private YNM quasi;

    /**
     * The dimension for the Boolean Tuples.
     */
    private Integer dimension;

    /**
     * The aborter decides when to stop for models using SAT search.
     */
    private Abortion aborter;

    /**
     * Creates a new <code>Model</code> instance with a
     * mapping that assigns to all irrelevant function symbols
     * a constant interpretation. In the case of boolean tuples this instance
     * also uses SAT search to find models.
     * @param funcRep some dummy function representation.
     * @param irrelevant function symbols that do not need to be interpreted.
     * @param allowQuasiModels allow quasi models.
     * @param btInformation if not null, use boolean tuples. Encapsulate the
     * incremental SAT engine, the dimension of the tuples and an aborter.
     */
    private Model(
            final FunctionRepresentation funcRep,
            final Set<FunctionSymbol> irrelevant,
            final boolean allowQuasiModels,
            final boolean enforceQuasi,
            final Triple<Engine, Integer, Abortion> btInformation
            ) {
        this.carrierSetSize = funcRep.getCarrierSetSize();
        this.useBooleanTuples = (btInformation != null);
        if (this.useBooleanTuples) {
            this.engine = btInformation.x;
            this.dimension = btInformation.y;
            this.aborter = btInformation.z;
        }
        this.model = new HashMap<FunctionSymbol, FunctionRepresentation>();
        this.defaultRepresentation = funcRep;
        for (FunctionSymbol f : irrelevant) {
            this.model.put(f, funcRep.getConstantRepresentation(f.getArity()));
        }
        this.quasi = allowQuasiModels ? YNM.MAYBE : YNM.NO;
        if (enforceQuasi) {
            this.quasi = YNM.YES;
        }
    }

    /**
     * Overwrites the <code>toString</code>-method of
     * <code>Object</code>.
     *
     * @return a <code>String</code>-representation of this model
     */
    @Override
    public String toString() {
        String result = this.quasi + " {";
        Iterator iter = this.model.entrySet().iterator();
        boolean first = true;
        while (iter.hasNext()) {
            if (first) {
                first = false;
            } else {
                result += " |";
            }
            Map.Entry entry = (Map.Entry) iter.next();
            String val = entry.getValue().toString();
            final int padding = 10;
            while (val.length() < padding) {
                val = " " + val;
            }
            result += " " + ((FunctionSymbol) entry.getKey()).getName()
                + " := " + val;
        }

        return result + " }";

    }

    /**
     * checks whether this model is really a model of the given rule.
     * @param rule The rule to check against.
     * @return YES means it is a model, MAYBE means it is a quasi-model, NO
     * means it is no model.
     */
    private YNM models(final Rule rule) {
        int variableCount = rule.getVariables().size();

        if (variableCount > 0) {

            // If the rule contains variables, iterate over all
            // possible variable values and check if each
            // combination satisfies the rule

            YNM res = YNM.YES;
            ElementVectorIterator valueIter =
                new ElementVectorIterator(variableCount, this.carrierSetSize);
            while (valueIter.hasNext()) {

                Iterator<TRSVariable> variableIter =
                    rule.getVariables().iterator();
                Map<TRSVariable, ElementValue> varMap =
                    new HashMap<TRSVariable, ElementValue>();
                for (int value : valueIter.next()) {
                    varMap.put(variableIter.next(),
                            this.defaultRepresentation.getElementValue(value));
                }

                YNM localResult = this.satisfiesRule(rule, varMap);
                if (localResult == YNM.NO) {
                    return localResult;
                }
                if (localResult == YNM.MAYBE) {
                    res = YNM.MAYBE;
                }

            }

            return res;

        } else {

            // Check if rule without variables satisfies model

            return this.satisfiesRule(rule, null);
        }

    }

    /**
     * gives an iterator over all (quasi-)models of the rules in R. Moreover,
     * for the given signature interpretations are chosen. Usually, the
     * signature is the signature of R, or the signature of P \cup R. For the
     * irrelevant function symbols a constant interpretation is chosen
     * arbitrarily but fixed in the beginning of the search. The function
     * representation fixes the domain.
     * @param R
     * @param signature
     * @param btInformation if not null, use boolean tuples. Encapsulate the
     * incremental SAT engine, the dimension of the tuples and an aborter.
     * @return
     */
    public static Iterator<Pair<Boolean,Labeller>> getModelIterator(
            final Set<Rule> R,
            final Set<FunctionSymbol> signature,
            final Set<FunctionSymbol> irrelevant,
            final FunctionRepresentation funcRep,
            final boolean allowQuasiModels,
            final boolean enforceQuasi,
            final Triple<Engine, Integer, Abortion> btInformation
            ) {
        Model m = new Model(funcRep, irrelevant, allowQuasiModels,
                enforceQuasi, btInformation);
        if (btInformation != null
                && !(btInformation.x instanceof MINISAT2IncrementalEngine)) {
            Model.logger.log(Level.FINE, "The engine has to be an incremental"
                    + " SatEngine in order to use Boolean Tuples!");
            return null;
        }
        return m.getFullModelIterator(R, signature, irrelevant);
    }

    /**
     * Provide an iterator that returns all possible models for the given rules
     * with the given signature.
     * @param R Generate models which comply with these rules.
     * @param signature The function symbols that need to be interpreted.
     * @return An iterator for all possible models.
     */
    private Iterator<Pair<Boolean,Labeller>> getFullModelIterator(
            final Set<Rule> R,
            final Set<FunctionSymbol> signature,
            final Set<FunctionSymbol> irrelevant
            ) {
        if (this.useBooleanTuples) {
            return new Iterator<Pair<Boolean, Labeller>>() {
                private boolean initialized = false;
                private FormulaFactory<None> formulaFactory;
                private BSLTermInterpretor termInterpretor;
                private Formula<None> formula;
                private MiniSAT2IncrementalFileChecker satChecker;
                private int[] solution;
                private Formula<None> quasiVar;
                private YNM hasNext;
                private Formula<None> notThisModel;
                private int maxId;

                @Override
                public boolean hasNext() {
                    if (!this.initialized) {
                        this.initialize();
                        this.hasNext = YNM.MAYBE;
                        try {
                            this.solution =
                                this.satChecker.solve(
                                    this.formula, Model.this.aborter, true);
                        } catch (SolverException e) {
                            this.solution = null;
                        } catch (AbortionException e) {
                            this.solution = null;
                        }
                        this.maxId = this.formula.getId();
                    } else {
                        if (this.hasNext == YNM.MAYBE) {
                            // incremental!
                            if (this.solution != null) {
                                this.notThisModel = this.disallowModel();
                            }

                            this.notThisModel.label(this.maxId + 1);
                            this.maxId = this.notThisModel.getId();
                            try {
                                this.solution = this.satChecker.solveKeepObligation(
                                        this.notThisModel, Model.this.aborter);
                            } catch (AbortionException e) {
                                this.solution = null;
                            }
                        }
                    }
                    if (this.hasNext == YNM.MAYBE) {
                        this.hasNext = YNM.fromBool(this.solution != null);
                    }
                    return this.hasNext.toBool();
                }

                private Formula<None> disallowModel() {
                    Formula<None> modelFormula = this.termInterpretor.getModelFormula(this.solution);
                    Formula<None> notGood = this.formulaFactory.buildNot(modelFormula);
                    return notGood;
                }

                private void initialize() {
                    this.initialized = true;
                    this.formulaFactory =
                        ((SatEngine) Model.this.engine).getFormulaFactory();
                    this.satChecker = (MiniSAT2IncrementalFileChecker) Model.this.engine.getSATChecker();
                    this.termInterpretor = new BSLTermInterpretor();
                    boolean quasiOK = (Model.this.quasi != YNM.NO);
                    boolean enforceQuasi = (Model.this.quasi == YNM.YES);
                    this.formula = this.termInterpretor.init(
                            this.formulaFactory,
                            Model.this.dimension,
                            signature,
                            irrelevant,
                            quasiOK,
                            enforceQuasi
                            );
                    for (Rule rule : R) {
                        Formula<None> newFormula = this.termInterpretor.interpretRule(rule);
                        this.formula =
                            this.formulaFactory.buildAnd(
                                    this.formula,
                                    newFormula
                                    );
                    }
                    this.quasiVar = this.termInterpretor.getQuasiVar();

                }

                @Override
                public Pair<Boolean, Labeller> next() {
                    this.hasNext = YNM.MAYBE;
                    boolean isQuasi = this.inSolution(this.quasiVar);

                    int carrierSetSize = (int) Math.pow(2, Model.this.dimension);
                    FunctionRepresentation representation = new BooleanTupleFunctionRepresentation(carrierSetSize);
                    Labeller labeller = new BooleanTupleLabeller(representation, this.termInterpretor, this.solution);

                    return new Pair<Boolean, Labeller>(isQuasi, labeller);
                }

                private boolean inSolution(Formula<None> formula) {
                    if (this.solution != null) {
                        int id = formula.getId();
                        return this.solution[id-1] == id;
                    }
                    return false;
                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }
            };
        } else {
            int n = R.size();
            final List<Iterable<?>> iterators = new ArrayList<Iterable<?>>(n);
            for (Rule rule : R) {
                iterators.add(new ModelGeneratorForARule(rule));
            }

            final Iterator<?> outerIterator =
                new ModelGeneratorForManyIterables(iterators);

            return new Iterator<Pair<Boolean, Labeller>>() {

                private YNM hasNext = YNM.MAYBE;
                private Iterator<?> innerIterator = null;

                @Override
                public boolean hasNext() {
                    if (this.hasNext == YNM.MAYBE) {
                        while (true) {
                            if (this.innerIterator == null) {
                                if (outerIterator.hasNext()) {
                                    outerIterator.next();
                                    iterators.clear();
                                    for (FunctionSymbol f : signature) {
                                        if (!Model.this.model.containsKey(f)) {
                                            iterators.add(new FunctionSymbolGenerator(f));
                                        }
                                    }
                                    this.innerIterator = new ModelGeneratorForManyIterables(iterators);
                                } else {
                                    this.hasNext = YNM.NO;
                                    break;
                                }
                            } else {
                                if (this.innerIterator.hasNext()) {
                                    this.innerIterator.next();
                                    this.hasNext = YNM.YES;
                                    break;
                                } else {
                                    this.innerIterator = null;
                                }
                            }
                        }
                    }
                    return this.hasNext.toBool();
                }

                @Override
                public Pair<Boolean, Labeller> next() {
                    if (this.hasNext()) {
                        this.hasNext = YNM.MAYBE;
                        Map<FunctionSymbol, FunctionRepresentation> interpretation =
                            new LinkedHashMap<FunctionSymbol, FunctionRepresentation>(Model.this.model);

                        boolean quasi = (Model.this.quasi == YNM.YES);

                        return new Pair<Boolean, Labeller>(quasi, new FiniteLabeller(interpretation));
                    } else {
                        throw new NoSuchElementException();
                    }
                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }

            };
        }
    }

    /**
     * Determines, whether a <code>Model</code> with a specified
     * variable assignments satisfies a certain <code>Rule</code>.
     *
     * @param rule the <code>Rule</code> to verify
     * @param varMap a mapping between variables and
     * <code>ElementValue</code>s
     * @return YES if both sides are equal, MAYBE, if left > right and NO,
     * otherwise.
     */
    private YNM satisfiesRule(Rule rule, Map<TRSVariable, ElementValue> varMap) {

        int leftSide = this.evaluate(rule.getLeft(), varMap).getIntValue();
        int rightSide = this.evaluate(rule.getRight(), varMap).getIntValue();
        if (leftSide == rightSide) {
            return YNM.YES;
        }
        if (leftSide > rightSide && this.quasi != YNM.NO) {
            return YNM.MAYBE;
        }
        return YNM.NO;
    }

    /**
     * evaluates a given term according to the interpretation in this model
     * and a given variable assignment.
     * @param t
     * @param varAssignment
     * @return
     */
    private ElementValue evaluate(TRSTerm t, Map<TRSVariable, ElementValue> varAssignment) {
        if (t.isVariable()) {
            return varAssignment.get(t);
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionRepresentation repr = this.model.get(ft.getRootSymbol());
            List<? extends TRSTerm> args = ft.getArguments();
            List<ElementValue> argList = new ArrayList<ElementValue>(args.size());
            int i = 0;
            for (TRSTerm arg : args) {
                argList.add(repr.requiresArgument(i) ? this.evaluate(arg, varAssignment) : null);
                i++;
            }
            return repr.evaluate(argList);
        }
    }



    /**
     * adds a representation for f, asserts that it is valid (w.r.t. quasi)
     * and new.
     * @param f
     * @param repr
     * @return
     */
    private void addChoice(FunctionSymbol f, FunctionRepresentation repr) {
        if (Globals.useAssertions) {
            assert(!(this.quasi == YNM.YES && !repr.isWeaklyMonotonic()));
        }
        this.model.put(f, repr);
        if (this.quasi == YNM.MAYBE && !repr.isWeaklyMonotonic()) {
            this.quasi = YNM.NO;
        }

    }

    /**
     * sets the quasi flag to true
     * @return
     */
    private void chooseQuasi() {
        if (Globals.useAssertions) {
            assert(this.quasi != YNM.NO);
        }
        this.quasi = YNM.YES;
    }



    /**
     * retracts the given representation for f, and updates the quasi-status
     * to the previous (given) value.
     * @param f
     * @param prevQuasi
     */
    private void rejectChoice(FunctionSymbol f, YNM prevQuasi) {
        this.model.remove(f);
        this.quasi = prevQuasi;
    }

    /**
     * retracts the given representation for f, and updates the quasi-status
     * to the previous (given) value.
     * @param f
     * @param prevQuasi
     */
    private void rejectChoice(YNM prevQuasi) {
        this.quasi = prevQuasi;
    }


    private class FunctionSymbolGenerator implements Iterable<FunctionRepresentation> {

        private final FunctionSymbol f;
        private Iterator<FunctionRepresentation> iterator;
        FunctionRepresentation repr;
        private YNM prevQuasi;
        private boolean nextValid;

        public FunctionSymbolGenerator(FunctionSymbol f) {
            this.f = f;
        }

        public void reset() {
            this.prevQuasi = Model.this.quasi;
            this.iterator =
                Model.this.defaultRepresentation.getFunctionIterator(
                        this.f.getArity(), this.prevQuasi == YNM.YES);
            this.nextValid = false;
        }

        @Override
        public Iterator<FunctionRepresentation> iterator() {
            this.reset();
            return new Iterator<FunctionRepresentation>() {

                @Override
                public boolean hasNext() {
                    if (!FunctionSymbolGenerator.this.nextValid) {
                        FunctionSymbolGenerator.this.nextValid = true;
                        if (FunctionSymbolGenerator.this.iterator.hasNext()) {
                            FunctionSymbolGenerator.this.repr = FunctionSymbolGenerator.this.iterator.next();
                            Model.this.rejectChoice(FunctionSymbolGenerator.this.prevQuasi);
                            Model.this.addChoice(FunctionSymbolGenerator.this.f, FunctionSymbolGenerator.this.repr);
                        } else {
                            Model.this.rejectChoice(FunctionSymbolGenerator.this.f, FunctionSymbolGenerator.this.prevQuasi);
                            FunctionSymbolGenerator.this.repr = null;
                        }
                    }
                    return FunctionSymbolGenerator.this.repr != null;
                }

                @Override
                public FunctionRepresentation next() {
                    if (this.hasNext()) {
                        FunctionSymbolGenerator.this.nextValid = false;
                        return FunctionSymbolGenerator.this.repr;
                    } else {
                        throw new NoSuchElementException();
                    }
                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }

            };
        }

    }


    private class TermWalker {

        private final FunctionSymbol f;
        private final int n;
        private final TermWalker[] children;
        private Iterator<FunctionRepresentation> iterator;
        private FunctionRepresentation repr;

        private TermWalker(TRSTerm t) {
            this.iterator = null;
            if (t.isVariable()) {
                this.f = null;
                this.n = 0;
                this.children = null;
            } else {
                TRSFunctionApplication ft = (TRSFunctionApplication) t;
                this.f = ft.getRootSymbol();
                this.n = this.f.getArity();
                this.children = new TermWalker[this.n];
                int i = 0;
                for (TRSTerm arg : ft.getArguments()) {
                    this.children[i] = new TermWalker(arg);
                    i++;
                }
            }
        }

        private boolean walk(boolean init) {
            if (this.f == null) {
                return init; // for init return gotnew, otherwise return done
            } else {
                if (init) {
                    this.repr = Model.this.model.get(this.f);
                    if (this.repr == null) {
                        // we have to choose
                        this.iterator =
                            new FunctionSymbolGenerator(this.f).iterator();
                        this.repr = this.iterator.next();
                    } else {
                        // we do not need to choose
                        this.iterator = null;
                    }
                } else {
                    // we need a new argument
                    for (int i = this.n; i != 0;) {
                        i--;
                        if (this.repr.requiresArgument(i)) {
                            if (this.children[i].walk(false)) {
                                // okay, a child has found a successor
                                for (int j = i + 1; j != this.n; j++) {
                                    this.children[j].walk(true);
                                }
                                return true;
                            }
                        }
                    }

                    // none of the children has found a new interpretation,
                    // perhaps we have a new top-level interpretation
                    if (this.iterator != null) {
                        if (this.iterator.hasNext()) {
                            this.repr = this.iterator.next();
                        } else {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }

                // in init or new top-level interpretation we have to init the
                // arguments
                for (int i = 0; i != this.n; i++) {
                    if (this.repr.requiresArgument(i)) {
                        this.children[i].walk(true);
                    }
                }

                return true;
            }
        }
    }

    /**
     * Iterates over all models such that we can evaluate the term
     * with our representation.
     * @author thiemann
     *
     */
    private class ModelGeneratorForATerm implements Iterator<Object> {

        private TermWalker walker;
        private boolean firstRun;
        private YNM hasNext;

        public ModelGeneratorForATerm(TRSTerm term) {

            this.walker = new TermWalker(term);
            this.firstRun = true;
            this.hasNext = YNM.MAYBE;

        }

        @Override
        public boolean hasNext() {
            if (this.hasNext == YNM.MAYBE) {
                this.hasNext = YNM.fromBool(this.walker.walk(this.firstRun));
                this.firstRun = false;
            }
            return this.hasNext.toBool();
        }

        @Override
        public Object next() {
            if (this.hasNext()) {
                this.hasNext = YNM.MAYBE;
                return this;
            } else {
                throw new NoSuchElementException();
            }
        }

        public void reset() {
            this.firstRun = true;
            this.hasNext = YNM.MAYBE;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

    /**
     * computes one by one every extension of this model for a given rule.
     * @author thiemann
     */
    private class ModelGeneratorForARule implements Iterable<Object> {

        private final ModelGeneratorForATerm left;
        private final ModelGeneratorForATerm right;
        private YNM hasNext;
        private final Rule rule;
        private boolean useLeft;
        private YNM prevQuasi;

        public ModelGeneratorForARule(
                Rule rule
                ) {
            this.rule = rule;
            this.left = new ModelGeneratorForATerm(rule.getLeft());
            this.right = new ModelGeneratorForATerm(rule.getRight());
        }

        private void reset() {
            this.left.reset();
            this.right.reset();
            this.hasNext = YNM.MAYBE;
            this.useLeft = true;
            this.prevQuasi = Model.this.quasi;
        }

        @Override
        public Iterator<Object> iterator() {
            this.reset();
            return new Iterator<Object>() {
                @Override
                public boolean hasNext() {
                    if (ModelGeneratorForARule.this.hasNext == YNM.MAYBE) {
                        while (true) {
                            if (ModelGeneratorForARule.this.useLeft) {
                                if (ModelGeneratorForARule.this.left.hasNext()) {
                                    ModelGeneratorForARule.this.left.next();
                                    ModelGeneratorForARule.this.right.reset();
                                    ModelGeneratorForARule.this.useLeft = false;
                                } else {
                                    ModelGeneratorForARule.this.hasNext = YNM.NO;
                                    Model.this.rejectChoice(ModelGeneratorForARule.this.prevQuasi);
                                    break;
                                }
                            } else {
                                // next right element
                                if (ModelGeneratorForARule.this.right.hasNext()) {
                                    ModelGeneratorForARule.this.right.next();
                                    YNM ruleModelled = Model.this.models(ModelGeneratorForARule.this.rule);
                                    if (ruleModelled != YNM.NO) {
                                        if (ruleModelled == YNM.MAYBE) {
                                            // if we have only have a quasi rule, then we must set quasi flag
                                            Model.this.chooseQuasi();
                                        }
                                        ModelGeneratorForARule.this.hasNext = YNM.YES;
                                        break;
                                    }
                                } else {
                                    ModelGeneratorForARule.this.useLeft = true;
                                }
                            }
                        }
                    }
                    return ModelGeneratorForARule.this.hasNext.toBool();
                }

                @Override
                public Object next() {
                    if (this.hasNext()) {
                        ModelGeneratorForARule.this.hasNext = YNM.MAYBE;
                        return this;
                    } else {
                        throw new NoSuchElementException();
                    }
                }

                @Override
                public void remove() {
                    throw new UnsupportedOperationException();
                }

            };
        }
    }

    private class ModelGeneratorForManyIterables implements Iterator<Object> {

        private final Iterable<?>[] iterables;
        private final Iterator<?>[] iterator;
        private final int n;
        private int i;
        private boolean goDown;
        private YNM hasNext;

        public ModelGeneratorForManyIterables(Collection<? extends Iterable<?>> iterables) {
            this.n = iterables.size();
            this.goDown = true;
            this.i = -1;
            this.iterator = new Iterator[this.n];
            this.iterables = iterables.toArray(new Iterable[this.n]);
            this.hasNext = YNM.MAYBE;
        }

        @Override
        public boolean hasNext() {
            if (this.hasNext == YNM.MAYBE) {
                while (true) {
                    if (this.goDown) {
                        this.i++;
                        if (this.i == this.n) {
                            this.hasNext = YNM.YES;
                            break;
                        } else {
                            this.iterator[this.i] = this.iterables[this.i].iterator();
                            this.goDown = false;
                        }
                    } else {
                        if (this.i == -1) {
                            this.hasNext = YNM.NO;
                            break;
                        }
                        Iterator<?> iter = this.iterator[this.i];
                        if (iter.hasNext()) {
                            iter.next();
                            this.goDown = true;
                        } else {
                            this.iterator[this.i] = null;
                            this.i--;
                        }
                    }
                }
            }
            return this.hasNext.toBool();
        }

        @Override
        public Object next() {
            if (this.hasNext()) {
                this.hasNext = YNM.MAYBE;
                this.i--;
                this.goDown = false;
                return this;
            } else {
                throw new NoSuchElementException();
            }
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
}
