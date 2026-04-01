package aprove.verification.oldframework.IntTRS.RankingRedPair;

import java.math.*;
import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import aprove.*;
import aprove.runtime.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.CoefficientConstraint.*;
import aprove.verification.oldframework.IntTRS.Ranking.*;
import aprove.verification.oldframework.IntTRS.RankingRedPair.RankingRedPairProcessor.*;
import aprove.verification.oldframework.IntTRS.RankingRedPair.RankingRedPairProcessor.Arguments;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Such a worker is spawned by the processor to ensure thread safeness.
 * @author Matthias Hoelzel
 */
public class RankingRedPairWorker {

    /**
     * Used for naming argument variables which arose due to massaging
     * to search for quadratic ranking functions.
     */
    private static final String SQUARE_INFIX = "sq_";

    /**
     * Used for naming argument variables which arose due to massaging
     * to search for ranking functions on absolutes of arguments.
     */
    private static final String ABS_INFIX = "abs_";

    /** Log, log, log. */
    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.IntTRS.RankingRedPair.RankingRedPairWorker");

    /** Set of original rules (pre-massaging) */
    private final Set<IGeneralizedRule> originalRules;

    /** Set of massaged rules (we build our arithmetic constraints from them) */
    private Map<IGeneralizedRule, IGeneralizedRule> massagedToOriginalRules;

    /** Set of transition relations, which arise from translating the massaged rules. */
    private LinkedHashSet<TransitionRelation> transitionRelations;

    /** Stores the origin of the transition relations (in the massaged rules). */
    private LinkedHashMap<TransitionRelation, IGeneralizedRule> history;

    /**
     * Stores all function symbols which aren't predefined and
     * which occur in the original rules.
     */
    private LinkedHashSet<FunctionSymbol> originalSymbols;

    /**
     * Stores all function symbols which aren't predefined and
     * which occur in the massaged rules, mapping them to their originals.
     */
    private Map<FunctionSymbol, FunctionSymbol> massagedToOriginalSymbols;

    /** Stores the monomials, which are needed to generate the interpretation */
    private LinkedHashMap<FunctionSymbol, LinkedHashSet<IndefinitePart>> importantMonomials;

    /**
     * The template for the polynomial interpretation for the /massaged/ symbols,
     * which contains indefinite coefficients.
     */
    private LinkedHashMap<FunctionSymbol, VarPolynomial> interpretationTemplate;

    /**
     * a list of constraints c = 0 where is a coefficient of some non-linear monomial.
     * useful, if linear interpretations have to be enforced.
     */
    private List<CoefficientConstraint> nonLinearCoefficientConstraints;

    /**
     * Stores the weak constraints, expressing that a given rule is oriented
     * weakly, for every transition relation/rule.
     */
    private LinkedHashMap<TransitionRelation, List<CoefficientConstraint>> weakConstraints;

    /**
     * See weakConstraint. The only difference is that these constraints express
     * strict decreasing.
     */
    private LinkedHashMap<TransitionRelation, List<CoefficientConstraint>> strictConstraints;

    /**
     * Constrains expressing ensuring that the interpretation is bounded.
     */
    private LinkedHashMap<TransitionRelation, List<CoefficientConstraint>> boundedConstraints;

    /**
     * expressions for bounds
     */
    private LinkedHashMap<TransitionRelation, SimplePolynomial> bounds;

    /** The final result! */
    private List<Set<IGeneralizedRule>> resultRules;

    /** The proof we are going to create! */
    private final RankingReductionPairProof proof;

    /** Arguments, which are given to the processor! */
    private final Arguments arguments;

    /**
     * Massages our rules.
     */
    private final Massager massager;

    /** Generates fresh names */
    private final FreshNameGenerator ng;

    /** Some aborter! */
    private final Abortion aborter;

    /**
     * It is a constructor; initialize the fields.
     * @param prob the current problem
     * @param rrpProof the proof we are going to create
     * @param args the current arguments
     * @param abortion some aborter
     */
    public RankingRedPairWorker(
        final IRSProblem prob,
        final RankingReductionPairProof rrpProof,
        final Arguments args,
        final Abortion abortion)
    {
        this.originalRules = prob.getRules();
        this.proof = rrpProof;
        this.arguments = args;
        this.aborter = abortion;
        this.massager = Massager.create(args.template, args.linearizeAll, abortion);

        // previously used names are not quite fresh
        final Set<String> predefinedNames = new LinkedHashSet<>(IDPPredefinedMap.DEFAULT_MAP.getUsedNames());
        predefinedNames.addAll(prob.getUsedNames());
        this.ng = new FreshNameGenerator(predefinedNames, FreshNameGenerator.APPEND_NUMBERS);
    }

    /**
     * Starts the whole process.
     * @return a transformed problem
     * @throws AbortionException can be aborted
     */
    public List<Set<IGeneralizedRule>> work() throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("reduction");
            l.logln("Here is the problem:");
            for (final IGeneralizedRule iRule : this.originalRules) {
                l.logln(iRule);
            }
        }

        // 1. Massage rules:
        long nanos1 = System.nanoTime();
        this.massageRules();
        long nanos2 = System.nanoTime();
        RankingRedPairWorker.log.finer("RRP: Massaging rules took " + (nanos2 - nanos1) / 1000000L + " ms");
        nanos1 = System.nanoTime();

        // 2. Translate the rules into relations:
        this.translateRules();
        nanos2 = System.nanoTime();
        RankingRedPairWorker.log.finer("RRP: Translating rules to transition relations took " + (nanos2 - nanos1) / 1000000L + " ms");
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("reduction");
            l.logln("Translated into relations:");
            for (final TransitionRelation tr : this.transitionRelations) {
                l.logln(tr);
            }
        }

        // 3. Generate constraints to be solved:
        nanos1 = System.nanoTime();
        this.generateCoefficientConstraints();
        nanos2 = System.nanoTime();
        RankingRedPairWorker.log.finer("RRP: Generating coefficient constraints took " + (nanos2 - nanos1) / 1000000L + " ms");

        // 4. Solve constraints & create result
        this.solveConstraints();

        // 5. Return result:
        return this.resultRules;
    }

    /**
     * Massages the original rules. That is, creates a bunch of rules
     * with possibly new function symbols (possibly with more arguments)
     * so that from a linear interpretation for them satisfying certain
     * constraints we will also get a (possibly non-linear)
     * interpretation satisfying the corresponding constraints.
     *
     * @throws AbortionException
     */
    private void massageRules() throws AbortionException {
        for (final IGeneralizedRule originalRule : this.originalRules) {
            this.massager.massage(originalRule, this.ng);
            //this.massagedToOriginalRules.put(massagedRule, originalRule);
        }
        this.massagedToOriginalSymbols = this.massager.getMassagedSymsToOriginalSyms();
        this.massagedToOriginalRules = this.massager.getMassagedRulesToOriginalRules();
    }

    /**
     * Rewrites the given rules into transition relations.
     * @throws AbortionException can be aborted
     */
    private void translateRules() throws AbortionException {
        final RuleToTransitionRelation ruleToRelation = new RuleToTransitionRelation(this.ng, this.aborter);
        final int size = this.originalRules.size();
        this.transitionRelations = new LinkedHashSet<>(size);
        this.history = new LinkedHashMap<>(size);

        for (final IGeneralizedRule iRule : this.massagedToOriginalRules.keySet()) { //this.originalRules) {
            this.aborter.checkAbortion();
            // only consider linear constraints in certified mode
            boolean linearOnly = !Options.certifier.isNone();
            final TransitionRelation newTR =
                ruleToRelation.ruleToTransitionRelation(iRule, this.arguments.freeVariableElimination, linearOnly);
            assert newTR != null : "new relation is null!";
            this.transitionRelations.add(newTR);
            this.registerOrigin(newTR, iRule);
        }
    }

    /**
     * Generates the constraints we have to solve in order to obtain a reduction
     * pair.
     * @throws AbortionException can be aborted
     */
    private void generateCoefficientConstraints() throws AbortionException {
        // 1. Generate following inequalities
        this.generateFollowingInequalities();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("reduction");
            l.logln("Obtained the following relations:");
            for (final TransitionRelation tr : this.transitionRelations) {
                l.logln(tr);
            }
        }

        // 2. Find symbols
        this.findSymbols();

        // 3. Find important monomials
        this.findImportantMonomials();
        this.aborter.checkAbortion();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("reduction");
            l.logln("Important monomials:");
            for (final Entry<FunctionSymbol, LinkedHashSet<IndefinitePart>> e : this.importantMonomials.entrySet()) {
                l.logln(e.getKey() + ":");
                l.logln(e.getValue());
                l.logln();
            }
        }

        // 4. Generate template for the polynomial order
        this.generatePoloTemplate();

        // 5. Put everything together and generate the constraints
        this.formulateCoefficientConstraints();
    }

    /**
     * Enriches the constraints by adding more constraints (using polynomials of
     * higher degrees) that are following from the original constraints.
     * @throws AbortionException can be aborted
     */
    private void generateFollowingInequalities() throws AbortionException {
        if (!this.arguments.generateFollowingInequalities) {
            return;
        }

        final LinkedHashSet<TransitionRelation> newRelations = new LinkedHashSet<>(this.transitionRelations.size());

        for (final TransitionRelation tr : this.transitionRelations) {
            final ConstraintsEnrichment ce = new ConstraintsEnrichment(tr, this.arguments, this.aborter);
            final TransitionRelation enrichedRelation = ce.enrich();

            this.registerOrigin(enrichedRelation, tr);
            newRelations.add(enrichedRelation);
        }

        this.transitionRelations = newRelations;
    }

    /**
     * Finds occurring function symbols.
     */
    private void findSymbols() {
        this.originalSymbols = new LinkedHashSet<>();

        for (final IGeneralizedRule iRule : this.originalRules) {
            this.originalSymbols.add(iRule.getLeft().getRootSymbol());
            this.originalSymbols.add(((TRSFunctionApplication) iRule.getRight()).getRootSymbol());
        }
    }

    /**
     * Finds the monomials we need to create the polynomial interpretation.
     */
    private void findImportantMonomials() {
        this.importantMonomials = new LinkedHashMap<>();

        for (final TransitionRelation tr : this.transitionRelations) {
            this.collectImportantMonomials(tr.getLeftMonomials(), tr.getStartSymbol(), tr.getStartVariables());
            this.collectImportantMonomials(tr.getRightMonomials(), tr.getEndSymbol(), tr.getEndVariables());
        }
    }

    /**
     * Collects the important monomials fill them correctly into
     * this.importantMonomials.
     * @param candidates a collection of candidate monomials
     * @param symbol the current symbol
     * @param variables the allowed variables
     */
    private void collectImportantMonomials(
        final Collection<IndefinitePart> candidates,
        final FunctionSymbol symbol,
        final List<TRSVariable> variables)
    {
        final LinkedHashMap<String, String> renaming = this.getStandardRenaming(symbol, variables);

        // We have to rename the candidates, because we cannot expect
        // that the arguments always have the same names. Thus, we use
        // a standard name that only depends on the symbol and the position of the argument:
        final LinkedHashSet<IndefinitePart> renamedCandidates = new LinkedHashSet<>(candidates.size());
        for (final IndefinitePart candidate : candidates) {
            renamedCandidates.add(candidate.rename(renaming));
        }

        if (!this.importantMonomials.containsKey(symbol)) {
            // If we see the symbol for the first time, then
            // we add all (renamed) variables:
            this.importantMonomials.put(symbol, renamedCandidates);
        } else {
            // Otherwise we take the intersection, because
            // we consider a monomial to be important if it
            this.importantMonomials.get(symbol).retainAll(renamedCandidates);
            // occurs "everywhere" where also the symbol occurs.
        }
    }

    /**
     * Returns a substitution for polynomial, to rename the first argument of an
     * f-term "f_1" & the second "f_2" & etc. We need this, because otherwise we
     * cannot expect that the argument no. x always has the same name.
     * @param prefix some additional prefix
     * @param symbol the symbol f
     * @param variables variables representing the arguments
     * @return LinkedHashMap
     */
    private LinkedHashMap<String, String> getStandardRenaming(
        final String prefix,
        final FunctionSymbol symbol,
        final List<TRSVariable> variables)
    {
        final LinkedHashMap<String, String> result = new LinkedHashMap<>();

        int position = 0;
        for (final TRSVariable var : variables) {
            position++;
            final String name = var.getName();

            //ugly hack for nicer names
            String newName;
            switch (this.arguments.template) {
            case CLASSIC:
                newName = prefix + symbol.getName() + '_' + position;
                break;
            case QUADRATIC:
                int arity = symbol.getArity();
                if (Globals.useAssertions) {
                    assert arity % 2 == 0 : symbol
                        + " has arity "
                        + arity
                        + ", but massaging for quadratic ranking functions should give symbols with an even number of arguments!";
                }
                int halfArity = arity / 2;
                if (position > halfArity) { // it's a square!
                    final int squarePosition = position - halfArity;
                    newName = prefix + RankingRedPairWorker.SQUARE_INFIX + symbol.getName() + '_' + squarePosition;
                } else {
                    newName = prefix + symbol.getName() + '_' + position;
                }
                break;
            case ABS:
                arity = symbol.getArity();
                if (Globals.useAssertions) {
                    assert arity % 2 == 0 : symbol
                        + " has arity "
                        + arity
                        + ", but massaging for absolute ranking functions should give symbols with an even number of arguments!";
                }
                halfArity = arity / 2;
                if (position > halfArity) { // it's an absolute!
                    final int absPosition = position - halfArity;
                    newName = prefix + RankingRedPairWorker.ABS_INFIX + symbol.getName() + '_' + absPosition;
                } else {
                    newName = prefix + symbol.getName() + '_' + position;
                }
                break;
            default:
                throw new IllegalStateException("Unknown template " + this.arguments.template);
            }
            result.put(name, newName);
        }

        return result;
    }

    /**
     * Returns a substitution for polynomial, to rename the first argument of an
     * f-term "f_1" & the second "f_2" & etc.
     * @param symbol the symbol f
     * @param variables variables representing the arguments
     * @return LinkedHashMap
     */
    private LinkedHashMap<String, String> getStandardRenaming(
        final FunctionSymbol symbol,
        final List<TRSVariable> variables)
    {
        return this.getStandardRenaming("", symbol, variables);
    }

    /**
     * Generate the template for the polynomial interpretation. This template
     * uses unknown coefficients those value are going to be determined by the
     * SMT-Solver.
     */
    private void generatePoloTemplate() {
        this.interpretationTemplate = new LinkedHashMap<>(this.massagedToOriginalSymbols.size());
        this.nonLinearCoefficientConstraints = new ArrayList<>();

        // Generate the template for the interpretation itself:
        for (final FunctionSymbol symbol : this.massagedToOriginalSymbols.keySet()) { //this.originalSymbols) {
            // Get the monomials, which have been calculated in the previous step:
            final LinkedHashSet<IndefinitePart> currentMonomials = this.importantMonomials.get(symbol);
            final LinkedHashMap<IndefinitePart, SimplePolynomial> templatePolyMap =
                new LinkedHashMap<>(currentMonomials.size());

            // Invent some new names for the coefficients (unknown values at the moment)
            for (final IndefinitePart mono : currentMonomials) {
                SimplePolynomial coeff = SimplePolynomial.create(this.ng.getFreshName("l", false));
                templatePolyMap.put(mono, coeff);
                if (!mono.isLinear() && !Options.certifier.isNone()) {
                    CoefficientConstraint c = new CoefficientConstraint(coeff, CoefficientConstraintType.EQ_ZERO);
                    this.nonLinearCoefficientConstraints.add(c);
                }
            }
            // Constant part:
            templatePolyMap.put(IndefinitePart.ONE, SimplePolynomial.create(this.ng.getFreshName("l", false)));

            this.interpretationTemplate.put(symbol, VarPolynomial.create(ImmutableCreator.create(templatePolyMap)));
        }
    }

    /**
     * Generate linear combination for the given transition relation, i.e. it
     * invents some (yet unknown) coefficients, multiplies the inequalities with
     * these coefficients & adds them.
     * @param tr input relation
     * @param useConstants adds a coefficient for an unknown constant
     * @return LinearCombination
     * @throws AbortionException can be aborted
     */
    private LinearCombination getLinearCombination(final TransitionRelation tr, final boolean useConstants)
        throws AbortionException
    {
        final LinearCombination lc = tr.getPCS().toLinearCombination(this.ng);
        final LinkedHashMap<String, String> renaming =
            this.getStandardRenaming("left", tr.getStartSymbol(), tr.getStartVariables());
        renaming.putAll(this.getStandardRenaming("right", tr.getEndSymbol(), tr.getEndVariables()));

        final LinearCombination combination = lc.rename(renaming);

        if (useConstants) {
            // Use constantCoeffName1 for 1 >= 1
            // and constantCoeffname2 for 1 <= 1.
            final String constantCoeffName1 = this.ng.getFreshName("coeff1", false);
            final String constantCoeffName2 = this.ng.getFreshName("coeff2", false);
            final LinearCombination resultComb =
                new LinearCombination(combination.getLeftSide().plus(
                    VarPolynomial.createCoefficient(constantCoeffName1).minus(
                        VarPolynomial.createCoefficient(constantCoeffName2))), combination.getRightSide().plus(
                    SimplePolynomial.create(constantCoeffName1).minus(SimplePolynomial.create(constantCoeffName2))));

            return resultComb;
        } else {
            return combination;
        }
    }

    /**
     * Formulates the constraints: The invented coefficients have to be >= 0 and
     * every rules has to be oriented weakly while at least one rule has to be
     * oriented strictly.
     * @throws AbortionException can be aborted
     */
    private void formulateCoefficientConstraints() throws AbortionException {
        this.weakConstraints = new LinkedHashMap<>(this.transitionRelations.size());
        this.strictConstraints = new LinkedHashMap<>(this.transitionRelations.size());
        this.boundedConstraints = new LinkedHashMap<>(this.transitionRelations.size());
        this.bounds = new LinkedHashMap<>(this.transitionRelations.size());

        for (final TransitionRelation tr : this.transitionRelations) {
            this.aborter.checkAbortion();
            final List<CoefficientConstraint> weakAtoms = new LinkedList<>();
            final List<CoefficientConstraint> strictAtoms = new LinkedList<>();
            final List<CoefficientConstraint> boundAtoms = new LinkedList<>();

            // 1. Generate formula, expressing that "the rule is decreasing":
            // Build the interpretation of the left & right side using the template.
            final LinearCombination lcDecrease = this.getLinearCombination(tr, true);
            final VarPolynomial leftInterpretationSide =
                RankingRedPairWorker.getPrefixRenamedPolynomial(this.interpretationTemplate.get(tr.getStartSymbol()), "left");
            final VarPolynomial rightInterpretationSide =
                RankingRedPairWorker.getPrefixRenamedPolynomial(this.interpretationTemplate.get(tr.getEndSymbol()), "right");

            // The linear combination must be equal to be template of our interpretation.
            final VarPolynomial diffTemplate = leftInterpretationSide.minus(rightInterpretationSide);
            RankingRedPairWorker.addIsZeroConstraints(lcDecrease.getLeftSide().minus(diffTemplate), weakAtoms);

            // The coefficients have to be >= 0, because otherwise we do not obtain valid
            // inequalities.
            RankingRedPairWorker.addAreGEZeroConstraints(lcDecrease.getCoefficients(), weakAtoms);

            // The rule is called "weakly-decreasing", iff the interpretation
            // of the left side minus the interpretation of the right side is >= 0.
            // Since we already ensured that the linear combination has to be our
            // interpretation, we only need to formulate that the right side of the
            // linear combination is >= 0:
            weakAtoms.add(new CoefficientConstraint(lcDecrease.getRightSide(), CoefficientConstraintType.GE_ZERO));

            // If the rule is "strictly-decreasing", then the right side has to be > 0:
            strictAtoms.add(new CoefficientConstraint(lcDecrease.getRightSide(), CoefficientConstraintType.GT_ZERO));

            // 2. Formulate constraints that the interpretation is bounded by some constant:
            // The rule is called "strictly-decreasing", iff the "interpretation decreases" (that
            // has already been formulated) and a "lower bound for the interpretation" exists, which
            // means that we have to find a inequality of the form
            // "interpretation of left side" > constant.
            final LinearCombination lcBound = this.getLinearCombination(tr, true);
            RankingRedPairWorker.addIsZeroConstraints(lcBound.getLeftSide().minus(leftInterpretationSide), boundAtoms);
            RankingRedPairWorker.addAreGEZeroConstraints(lcBound.getCoefficients(), boundAtoms);
            this.bounds.put(tr, lcBound.getRightSide());

            this.weakConstraints.put(tr, weakAtoms);

            if (this.arguments.useGeneralizedReductionPairs) {
                this.strictConstraints.put(tr, strictAtoms);
                this.boundedConstraints.put(tr, boundAtoms);
            } else {
                this.strictConstraints.put(tr, strictAtoms);
                this.strictConstraints.get(tr).addAll(boundAtoms);
            }
        }
    }

    /**
     * Formulates constraints that a given polynomial is identically zero, i.e.
     * every coefficient must be zero.
     * @param toBeZero the input polynomial
     * @param constraints list of constraints to be filled
     */
    private static
        void
        addIsZeroConstraints(final VarPolynomial toBeZero, final List<CoefficientConstraint> constraints)
    {
        for (final SimplePolynomial simple : toBeZero.getVarMonomials().values()) {
            constraints.add(new CoefficientConstraint(simple, CoefficientConstraintType.EQ_ZERO));
        }
    }

    /**
     * Formulates the constraints, that every coefficient occurring in the a
     * given collection is >= 0.
     * @param coefficients collection of coefficients (Strings)
     * @param constraints list of constraints to be completed
     */
    private static void addAreGEZeroConstraints(
        final Collection<String> coefficients,
        final List<CoefficientConstraint> constraints)
    {
        for (final String coefficient : coefficients) {
            constraints.add(new CoefficientConstraint(
                SimplePolynomial.create(coefficient),
                CoefficientConstraintType.GE_ZERO));
        }
    }

    /**
     * Renames the variable occurring in the polynomial using the specified
     * prefix.
     * @param input some polynomial
     * @param prefix the prefix for every variable
     * @return another VarPolynomial
     */
    private static VarPolynomial getPrefixRenamedPolynomial(final VarPolynomial input, final String prefix) {
        final LinkedHashMap<String, VarPolynomial> renaming = new LinkedHashMap<>();

        for (final String v : input.getVariables()) {
            renaming.put(v, VarPolynomial.createVariable(prefix + v));
        }

        return input.substituteVariables(renaming);
    }

    /**
     * Invokes the SMT-Solver and obtains a solution (if possible).
     * @throws AbortionException can be aborted
     */
    private void solveConstraints() throws AbortionException {
        // 1. Build formula:
        final FormulaFactory<SMTLIBTheoryAtom> factory = new FullSharingFactory<>();
        final LinkedList<Formula<SMTLIBTheoryAtom>> resultFormulae = new LinkedList<>();

        // Feed the factory with the weak constraints and the non-linearity-constraints
        final List<TheoryAtom<SMTLIBTheoryAtom>> nlTheoryAtoms =
                factory.buildTheoryAtoms(RankingRedPairWorker.toTheoryAtoms(this.nonLinearCoefficientConstraints));
        final Formula<SMTLIBTheoryAtom> nlFormula = factory.buildAnd(nlTheoryAtoms);
        resultFormulae.add(nlFormula);
        for (final List<CoefficientConstraint> weakAtoms : this.weakConstraints.values()) {
            final List<TheoryAtom<SMTLIBTheoryAtom>> weakTheoryAtoms =
                factory.buildTheoryAtoms(RankingRedPairWorker.toTheoryAtoms(weakAtoms));
            final Formula<SMTLIBTheoryAtom> weakFormula = factory.buildAnd(weakTheoryAtoms);
            resultFormulae.add(weakFormula);
        }


        // Process the strict constraints
        final LinkedList<Formula<SMTLIBTheoryAtom>> strictFormulae = new LinkedList<>();
        for (final List<CoefficientConstraint> strictAtoms : this.strictConstraints.values()) {
            final List<TheoryAtom<SMTLIBTheoryAtom>> strictTheoryAtoms =
                factory.buildTheoryAtoms(RankingRedPairWorker.toTheoryAtoms(strictAtoms));
            final Formula<SMTLIBTheoryAtom> strictFormula = factory.buildAnd(strictTheoryAtoms);
            strictFormulae.add(strictFormula);
        }
        // Please note, that only one rule has to be oriented strictly.
        // Thus, we use a disjunction here:
        resultFormulae.add(factory.buildOr(strictFormulae));

        if (this.arguments.useGeneralizedReductionPairs) {
            // Process the bound constraints.
            // Please note that these bound are included in the strict constraints
            // when useGeneralizedReductionPairs is set to false.
            final LinkedList<Formula<SMTLIBTheoryAtom>> boundFormulae = new LinkedList<>();
            for (final List<CoefficientConstraint> boundAtoms : this.boundedConstraints.values()) {
                final List<TheoryAtom<SMTLIBTheoryAtom>> boundTheoryAtoms =
                    factory.buildTheoryAtoms(RankingRedPairWorker.toTheoryAtoms(boundAtoms));
                final Formula<SMTLIBTheoryAtom> boundFormula = factory.buildAnd(boundTheoryAtoms);
                boundFormulae.add(boundFormula);
            }
            resultFormulae.add(factory.buildOr(boundFormulae));
        }

        // 2. Invoke SMT-Solver:
        final SMTEngine smtEngine = new YicesEngine();
        try {
            final Pair<YNM, Map<String, String>> smtSolverResult =
                smtEngine.solve(resultFormulae, SMTLogic.QF_LRA, this.aborter);
            this.createResult(smtSolverResult);
        } catch (final WrongLogicException wle) {
            System.err.println("Solver exception: " + wle);
            this.createResult(new Pair<YNM, Map<String, String>>(YNM.MAYBE, null));
        }
    }

    /**
     * Rewrites a list of coefficient constraints as SMTLIBTheoryAtoms.
     * @param constraints list of CoefficientConstraints
     * @return list of SMTLIBTheoryAtoms
     */
    private static List<SMTLIBTheoryAtom> toTheoryAtoms(final List<CoefficientConstraint> constraints) {
        final List<SMTLIBTheoryAtom> result = new LinkedList<>();
        for (final CoefficientConstraint cc : constraints) {
            result.add(cc.toSMTLIBRatTheoryAtom());
        }
        return result;
    }

    /**
     * Creates the result.
     * @param smtSolverResult SMT-Solvers decision
     */
    private void createResult(final Pair<YNM, Map<String, String>> smtSolverResult) {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("reduction");
            l.logln("SMT-Solver said " + smtSolverResult.x);
        }
        if (smtSolverResult.x == YNM.YES) {
            final Set<IGeneralizedRule> removedDecreasingRules = new LinkedHashSet<>(this.originalRules.size() - 1);
            final Set<IGeneralizedRule> removedBoundedRules = new LinkedHashSet<>(this.originalRules.size() - 1);

            final Map<String, PreciseRational> ratModel = ToolBox.parseRationalInterpretation(smtSolverResult.y);
            PreciseRational minBnd = new PreciseRational(BigInteger.ZERO);

            // Calculate which rules can be dropped:
            final LinkedHashSet<IGeneralizedRule> droppedRulesDueToDecrease = new LinkedHashSet<>();
            final LinkedHashSet<IGeneralizedRule> droppedRulesDueToBoundedness = new LinkedHashSet<>();
            for (final TransitionRelation tr : this.transitionRelations) {
                if (Globals.DEBUG_MATTHIAS) {
                    assert RankingRedPairWorker.isSatisfied(this.weakConstraints.get(tr), ratModel) : "Weak constraints are not satisfied!!";
                }

                // two levels of indirection because of rule massaging
                final IGeneralizedRule massagedRule = this.history.get(tr);
                final IGeneralizedRule originalRule = this.massagedToOriginalRules.get(massagedRule);
                if (RankingRedPairWorker.isSatisfied(this.strictConstraints.get(tr), ratModel)) {
                    droppedRulesDueToDecrease.add(originalRule);
                    PreciseRational bnd =
                            ToolBox.evaluateSimplePolynomial(this.bounds.get(tr), ratModel);
                    minBnd = minBnd.compareTo(bnd) <= 0 ? minBnd : bnd;
                } else {
                    removedDecreasingRules.add(originalRule);
                }

                if (this.arguments.useGeneralizedReductionPairs) {
                    if (RankingRedPairWorker.isSatisfied(this.boundedConstraints.get(tr), ratModel)) {
                        droppedRulesDueToBoundedness.add(originalRule);
                        PreciseRational bnd =
                                ToolBox.evaluateSimplePolynomial(this.bounds.get(tr), ratModel);
                        minBnd = minBnd.compareTo(bnd) <= 0 ? minBnd : bnd;
                    } else {
                        removedBoundedRules.add(originalRule);
                    }
                }
            }

            // TODO: Fix the "dropped"-assert!
            //this.proof.setDroppedRules(droppedRules);
            this.proof.setBound(minBnd.getNumerator());
            this.proof.setModel(ratModel);
            this.proof.setTemplate(this.interpretationTemplate);

            this.resultRules = new LinkedList<>();
            if (this.arguments.useGeneralizedReductionPairs) {
                this.proof.setDroppedRulesDueToBoundedness(droppedRulesDueToBoundedness);
                if (removedBoundedRules.containsAll(removedDecreasingRules)) {
                    this.resultRules.add(removedBoundedRules);
                } else if (removedDecreasingRules.containsAll(removedBoundedRules)) {
                    this.resultRules.add(removedDecreasingRules);
                } else {
                    this.resultRules.add(removedDecreasingRules);
                    this.resultRules.add(removedBoundedRules);
                }
            } else {
                this.resultRules.add(removedDecreasingRules);
            }
            this.proof.setDroppedRulesDueToDecrease(droppedRulesDueToDecrease);
        } else {
            // We cannot delete any rules:
            this.resultRules = new LinkedList<>();
            this.resultRules.add(this.originalRules);
        }
    }

    /**
     * Calculates whether or not a list of coefficient constraints is satisfied
     * by an rational interpretation.
     * @param constraints the constraints to be checked
     * @param interpretation interpretation to be used
     * @return boolean
     */
    private static boolean isSatisfied(
        final List<CoefficientConstraint> constraints,
        final Map<String, PreciseRational> interpretation)
    {
        boolean result = true;

        for (final CoefficientConstraint cc : constraints) {
            if (!cc.isSatisfiedByRationalAssignment(interpretation)) {
                result = false;
                break;
            }
        }

        return result;
    }

    /**
     * Registers that tr was created from iRule.
     * @param tr some transition relation
     * @param iRule some IGeneralizedRule
     */
    private void registerOrigin(final TransitionRelation tr, final IGeneralizedRule iRule) {
        this.history.put(tr, iRule);
    }

    /**
     * Registers that newTR was created from oldTR.
     * @param newTR the new transition relation
     * @param oldTR the old transition relation
     */
    private void registerOrigin(final TransitionRelation newTR, final TransitionRelation oldTR) {
        assert this.history.containsKey(oldTR) : "oldTR is not registered!";
        this.history.put(newTR, this.history.get(oldTR));
    }
}
