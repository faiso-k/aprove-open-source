/**
 *
 */
package aprove.verification.oldframework.IRSwT.Engines;

import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.Engines.FormulaGenerators.*;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.*;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.AbstractFormula;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.AndFormula;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.Atom;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.Atom.*;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.OrFormula;
import aprove.verification.oldframework.IRSwT.Orders.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Synthesizes an interpretation that orients the rules.
 * @author Matthias Hoelzel
 *
 */
public class InterpretationOrderEngine extends AbstractOrderEngine {
    /**
     * Will contain all occurring non-predefined function symbols.
     */
    private final LinkedHashSet<FunctionSymbol> symbols;

    /**
     * Set of symbols for which some rule exist.
     */
    private final LinkedHashSet<FunctionSymbol> definedSymbols;

    /**
     * The result interpretation!
     */
    private Interpretation<PreciseRational> interpretation;

    /**
     * Stores the formulae for stirct decreases.
     */
    private final LinkedHashMap<IGeneralizedRule, AbstractFormula<Atom>> strictFormulae;

    /**
     * Stores the formulae for weak decreases.
     */
    private final LinkedHashMap<IGeneralizedRule, AbstractFormula<Atom>> weakFormulae;

    /**
     * Stores the formulae for the lower bounds.
     */
    private final LinkedHashMap<IGeneralizedRule, AbstractFormula<Atom>> boundFormulae;

    /**
     * The formula that is passed to the SMT-solver!
     */
    private AbstractFormula<Atom> formula;

    /** Formula factory!*/
    private final FullSharingFactory<SMTLIBTheoryAtom> factory;

    /**
     * Constructor!
     * @param rulesSet set of rules
     * @param sorts sort dictionary
     * @param fact some formula factory
     * @param abortion some aborter
     * @param freshGen some name generator
     */
    public InterpretationOrderEngine(
        final Set<IGeneralizedRule> rulesSet,
        final SortDictionary sorts,
        final FullSharingFactory<SMTLIBTheoryAtom> fact,
        final Abortion abortion,
        final FreshNameGenerator freshGen)
    {
        super(rulesSet, sorts, abortion, freshGen);
        this.symbols = new LinkedHashSet<>();
        this.factory = fact;
        this.strictFormulae = new LinkedHashMap<>();
        this.weakFormulae = new LinkedHashMap<>();
        this.boundFormulae = new LinkedHashMap<>();
        this.definedSymbols = new LinkedHashSet<>();
    }

    @Override
    protected AbstractOrder generateOrder() throws AbortionException {
        // 1. Find symbols
        this.findSymbols();

        // 2. Build interpretation template
        this.buildInterpretationTemplate();
        this.aborter.checkAbortion();

        // 3. Generate SMT-formulae
        this.generateSMTFormulae();

        // 4. Solve and try to generate order:
        return this.generateInterpretationOrder();
    }

    /**
     * Adds all non-predefined function symbol that occurs in some rule.
     */
    private void findSymbols() {
        for (final IGeneralizedRule rule : this.rules) {
            final TRSFunctionApplication left = rule.getLeft();
            final TRSTerm right = rule.getRight();
            this.collectSymbols(left);
            this.collectSymbols(right);
            this.registerDefinedSymbol(left);
            this.registerDefinedSymbol(right);
        }
    }

    /**
     * Adds every non-predefined function symbol to the field symbols.
     * @param t some term
     */
    private void collectSymbols(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol symbol = func.getRootSymbol();
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(symbol)) {
                this.symbols.add(symbol);
                for (final TRSTerm arg : func.getArguments()) {
                    this.collectSymbols(arg);
                }
            }
        }
    }

    /**
     * Adds the symbol to our set of defined symbols.
     * @param t left or right side of a rule
     */
    private void registerDefinedSymbol(final TRSTerm t) {
        assert t instanceof TRSFunctionApplication;
        this.definedSymbols.add(((TRSFunctionApplication) t).getRootSymbol());
    }

    /**
     * Generates an interpretation template.
     */
    private void buildInterpretationTemplate() {
        this.interpretation = new Interpretation<>(this.symbols, this.fng);
    }

    /**
     * Generates the SMT-formulae to be solved.
     * @throws AbortionException can be aborted
     */
    private void generateSMTFormulae() throws AbortionException {
        AbstractFormula<Atom> oneRuleIsStrict = new FalseFormula<>();
        AbstractFormula<Atom> oneRuleIsBounded = new FalseFormula<>();
        AbstractFormula<Atom> everyRuleIsWeak = new TrueFormula<>();

        for (final IGeneralizedRule rule : this.rules) {
            this.aborter.checkAbortion();
            final Set<Atom> preconditions = this.generatePreconditions(rule);

            final VarPolynomial leftInterpretation = this.interpretation.applyInterpretation(rule.getLeft(), this.fng);
            final VarPolynomial rightInterpretation =
                this.interpretation.applyInterpretation(rule.getRight(), this.fng);

            final AbstractFormula<Atom> strictFormula =
                this.generateStrictDecreaseFormula(leftInterpretation, rightInterpretation, preconditions);
            final AbstractFormula<Atom> weakFormula =
                this.generateWeakDecreaseFormula(leftInterpretation, rightInterpretation, preconditions);
            final AbstractFormula<Atom> boundFormula =
                this.generateLowerBoundFormula(leftInterpretation, preconditions);

            // Register the results:
            this.strictFormulae.put(rule, strictFormula);
            this.weakFormulae.put(rule, weakFormula);
            this.boundFormulae.put(rule, boundFormula);

            oneRuleIsStrict = new OrFormula<>(oneRuleIsStrict, strictFormula);
            oneRuleIsBounded = new OrFormula<>(oneRuleIsBounded, boundFormula);
            everyRuleIsWeak = new AndFormula<>(everyRuleIsWeak, weakFormula);
        }
        // To ensure that the generated precondition arising from the sorts are correct,
        // we need that certain coefficient are non-negative:
        final AbstractFormula<Atom> correctDomains = this.calculateCorrectCoefficientDomainFormula();

        // Put everything together:
        final AbstractFormula<Atom> oneStrictOneBounded = new AndFormula<>(oneRuleIsStrict, oneRuleIsBounded);
        final AbstractFormula<Atom> almostResult = new AndFormula<>(correctDomains, oneStrictOneBounded);
        this.formula = new AndFormula<>(everyRuleIsWeak, almostResult);
    }

    /**
     * Coefficients with correspond to TERM-sorted positions should be >= 0
     * to ensure that the additional preconditions calculated by collectSortPreconditions
     * are correct.
     * @return some formula
     * @throws AbortionException can be aborted
     */
    private AbstractFormula<Atom> calculateCorrectCoefficientDomainFormula() throws AbortionException {
        AbstractFormula<Atom> result = new TrueFormula<>();
        for (final FunctionSymbol sym : this.symbols) {
            this.aborter.checkAbortion();
            if (!this.definedSymbols.contains(sym)) {
                final VarPolynomial poly = this.interpretation.getInterpretationPolynomial(sym);
                for (final SimplePolynomial sp : poly.getAllCoefficients()) {
                    final VarPolynomial vpSp = VarPolynomial.create(sp);
                    final Atom coeffGEZero = new Atom(vpSp, AtomType.ATOM_GE, VarPolynomial.ZERO);
                    final AtomFormula<Atom> newConjunctionPart = new AtomFormula<Atom>(coeffGEZero);
                    result = new AndFormula<>(result, newConjunctionPart);
                }
                /*for (int p = 0; p < sym.getArity(); p++) {
                    if (this.sortDictionary.getSort(sym, p) == Sort.TERM) {
                        final String templateVarName = this.interpretation.getTemplateVariable(sym, p);
                        final VarPolynomial interpretationPoly = this.interpretation.getInterpretationPolynomial(sym);
                        final SimplePolynomial coefficient = interpretationPoly.getCoefficientPoly(templateVarName);
                        final VarPolynomial coefficientPoly = VarPolynomial.create(coefficient);
                        final Atom coefficientGEZero = new Atom(coefficientPoly, AtomType.ATOM_GE, VarPolynomial.ZERO);
                        result = new AndFormula<>(result, new AtomFormula<>(coefficientGEZero));
                    }
                }*/
            }
        }
        return result;
    }

    /**
     * Returns the rewritten condition and the sort preconditions.
     * @param rule some rule
     * @return set of atoms
     * @throws AbortionException can be aborted
     */
    private Set<Atom> generatePreconditions(final IGeneralizedRule rule) throws AbortionException {
        final LinkedHashSet<Atom> preconditions = new LinkedHashSet<>();
        final TRSTerm condition = rule.getCondTerm();
        if (condition != null) {
            assert condition instanceof TRSFunctionApplication : "Strange condition!";
            final List<PolynomialConstraint> pcs =
                ToolBox.boolTermToPolynomialConstraints((TRSFunctionApplication) condition, this.fng, this.aborter);
            for (final PolynomialConstraint pc : pcs) {
                preconditions.add(pc.toAtom());
            }
        }

        this.collectSortPreconditions(rule.getLeft(), preconditions);
        this.collectSortPreconditions(rule.getRight(), preconditions);

        return preconditions;
    }

    /**
     * Collects the sort preconditions, i.e., the interpretation of
     * @param t currently considered term
     * @param preconditions set of atoms to be completed
     */
    private void collectSortPreconditions(final TRSTerm t, final LinkedHashSet<Atom> preconditions) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                final ImmutableList<TRSTerm> args = func.getArguments();
                for (int p = 0; p < sym.getArity(); p++) {
                    final TRSTerm arg = args.get(p);
                    if (this.sortDictionary.getSort(sym, p) == Sort.FUNAPP && arg instanceof TRSVariable) {
                        final TRSVariable varArg = (TRSVariable) arg;
                        final String name = varArg.getName();
                        final VarPolynomial polyVarArg = VarPolynomial.createVariable(name);
                        preconditions.add(new Atom(polyVarArg, AtomType.ATOM_GE, VarPolynomial.ZERO));
                    } else {
                        this.collectSortPreconditions(arg, preconditions);
                    }
                }
            }
        }
    }

    /**
     * Generates a formula that expresses that the left side is >= the right side.
     * @param leftInterpretation some poly
     * @param rightInterpretation some poly
     * @param preconditions some preconditions
     * @return a formula
     */
    private AbstractFormula<Atom> generateWeakDecreaseFormula(
        final VarPolynomial leftInterpretation,
        final VarPolynomial rightInterpretation,
        final Set<Atom> preconditions)
    {
        return this
            .createFormulaGenerator(preconditions, leftInterpretation.minus(rightInterpretation))
            .generateFormula();
    }

    /**
     * Generates a formula that expresses that the left side is > the right side.
     * @param leftInterpretation some poly
     * @param rightInterpretation some poly
     * @param preconditions some preconditions
     * @return a formula
     */
    private AbstractFormula<Atom> generateStrictDecreaseFormula(
        final VarPolynomial leftInterpretation,
        final VarPolynomial rightInterpretation,
        final Set<Atom> preconditions)
    {
        return this.createFormulaGenerator(
            preconditions,
            leftInterpretation.minus(rightInterpretation).minus(VarPolynomial.ONE)).generateFormula();
    }

    /**
     * Generates a formula that expresses that the left side is >= 0.
     * @param leftInterpretation some poly
     * @param preconditions some preconditions
     * @return a formula
     */
    private AbstractFormula<Atom> generateLowerBoundFormula(
        final VarPolynomial leftInterpretation,
        final Set<Atom> preconditions)
    {
        return this.createFormulaGenerator(preconditions, leftInterpretation).generateFormula();
    }

    /**
     * Generates some instance of a formula generator using the given parameters.
     * @param atoms set of preconditions (atoms)
     * @param poly a polynomial to be >= 0
     * @return a formula generator
     */
    private AbstractFormulaGenerator createFormulaGenerator(final Set<Atom> atoms, final VarPolynomial poly) {
        return new SimpleFormulaGenerator(atoms, poly, this.fng);
    }

    /**
     * Generates the concrete interpretation order.
     * @return order
     * @throws AbortionException can be aborted
     */
    private AbstractOrder generateInterpretationOrder() throws AbortionException {
        this.aborter.checkAbortion();
        final Formula<SMTLIBTheoryAtom> smtFormula = this.formula.toSMTLIBInt(this.factory);

        final LinkedList<Formula<SMTLIBTheoryAtom>> singletonList = new LinkedList<>();
        singletonList.add(smtFormula);

        final SMTEngine smtEngine = new SMTLIBEngine();
        try {
            final Pair<YNM, Map<String, String>> result = smtEngine.solve(singletonList, SMTLogic.QF_NIA, this.aborter);
            /*if (Globals.DEBUG_MATTHIAS) {
                System.err.println(result.x);
            }*/
            if (result.x == YNM.YES) {
                // Parse the model:
                final Map<String, String> rawModel = result.y;
                final Map<String, PreciseRational> model = ToolBox.parseRationalInterpretation(rawModel);

                // Check whether or not the formula is really true:
                if (!this.formula.check(model)) {
                    if (Globals.DEBUG_MATTHIAS) {
                        System.err.println("SMT-Solver is buggy:");
                        System.err.println("Model:" + rawModel);
                        System.err.println("Original formula:" + this.formula.toString());
                        System.err.println("SMT-formula:" + smtFormula.toString());
                    }

                    return null;
                }

                final LinkedHashSet<IGeneralizedRule> boundedRules = new LinkedHashSet<>();
                final LinkedHashSet<IGeneralizedRule> strictRules = new LinkedHashSet<>();

                for (final IGeneralizedRule rule : this.rules) {
                    if (this.strictFormulae.get(rule).check(model)) {
                        strictRules.add(rule);
                    }
                    if (this.boundFormulae.get(rule).check(model)) {
                        boundedRules.add(rule);
                    }
                    if (Globals.DEBUG_MATTHIAS) {
                        assert this.weakFormulae.get(rule).check(model) : "Validity should have been checked!";
                    }
                }
                if (Globals.DEBUG_MATTHIAS) {
                    assert !strictRules.isEmpty() && !boundedRules.isEmpty() : "Validity should have been checked!";
                }
                this.interpretation.instantiateCoefficients(model);
                return new InterpretationOrder<>(this.rules, this.interpretation, strictRules, boundedRules);
            }
        } catch (final WrongLogicException wle) {
            System.err.println(wle);
            wle.printStackTrace();
        }

        // Error or no model! -> No result!
        return null;
    }
}
