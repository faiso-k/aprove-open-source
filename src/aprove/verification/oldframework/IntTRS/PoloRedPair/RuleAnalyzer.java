package aprove.verification.oldframework.IntTRS.PoloRedPair;

import static java.util.stream.Collectors.*;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.runtime.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.CoefficientConstraint.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.IntTRSPolynomialOrderProcessor.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.PolynomialConstraint.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Finds and applies a polynomial interpretation for the given integer-based TRS
 * ("KITTeLProblem"). Please note, that at this we assume, that the rules have
 * been prepared using RulePrepartion. TODO: Find a better solution for
 * substitutions! TODO: Clean up this mess! TODO: Introduce Graph-cache TODO:
 * Start terms TODO: Store deleted rules .. to allow appliance of model checkers
 * @author Matthias Hoelzel
 */
class RuleAnalyzer {
    /** Set of integer-based rules ("KITTeL-Rules") */
    private final Set<IGeneralizedRule> rules;

    /** Final result. */
    private LinkedList<Set<IGeneralizedRule>> resultSystems;

    /** List of polynomial constraints restricting the arguments. */
    private LinkedHashMap<IGeneralizedRule, List<PolynomialConstraint>> argumentConstraints;

    /**
     * Set of variables, that should not be substituted. This will be calculated
     * by a heuristic.
     */
    private LinkedHashSet<String> substitutionAvoidanceSet;

    /** Stores [left]_interpretation - [right]_interpretation for each rule. */
    private LinkedHashMap<IGeneralizedRule, VarPolynomial> diffPolys;

    /** Stores [left]_interpretation for each rule. */
    private LinkedHashMap<IGeneralizedRule, VarPolynomial> leftPolys;

    /** Stores upper bounds. */
    private final LinkedHashMap<String, BigInteger> upperBounds;

    /** Stores lower bounds. */
    private final LinkedHashMap<String, BigInteger> lowerBounds;

    /**
     * Stores weak coefficient constraints. These constraints must be satisfied!
     */
    private LinkedHashMap<IGeneralizedRule, LinkedList<CoefficientConstraint>> weakCoefficientConstraints;

    /**
     * Stores strong coefficient constraints. These constraints can be
     * satisfied, but it is better to satisfy as many as possible, because then
     * the polynomial order will kill more rules. Depending on whether or not
     * the argument
     */
    private LinkedHashMap<IGeneralizedRule, LinkedList<CoefficientConstraint>> decreasingCoefficientConstraints;

    /**
     * Only used if the argument useGeneralReductionPairs is set to true. In
     * this case it will store inferred coefficients ensuring that a given rule
     * is bounded w.r.t. the polynomial interpretation. For instance the rule
     * f(x) -> ... | x > 0 is bounded w.r.t. Pol(f(x)) = x is > 0 for all
     * instantiations of x allowing to reduce further.
     */
    private LinkedHashMap<IGeneralizedRule, LinkedList<CoefficientConstraint>> boundedCoefficientConstraints;

    /** Stores the coefficients. */
    private Map<String, BigInteger> model;

    /** Dropped any rules? */
    // private boolean dropped;

    /** Set of occurring symbols */
    private final Set<FunctionSymbol> symbols;

    /** Aborter */
    private final Abortion aborter;

    /** The current interpretation */
    private PolynomialInterpretation interpretation;

    /** Should we use the upper or the lower bound? */
    private enum BoundUsage {
        /** Possible values are upper and lower! */
        USE_UPPER_BOUND, USE_LOWER_BOUND;
    };

    /** Heuristic whether we should use the upper bound or the lower bound. */
    private final LinkedHashMap<String, BoundUsage> boundHeuristic;

    /** Formula factory */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /** The proof to be built. */
    private final IntTRSPoloRedPairProof proof;

    /** The processor arguments. */
    private final PolynomialOrderArguments arguments;

    /** A name generator. */
    private final FreshNameGenerator ng;

    /**
     * Constructor Make sure that the rules have been prepared using
     * RulePrepartion!
     * @param intTRSRules the current intTRS rules
     * @param formulaFactory formula factory
     * @param gen a name generator
     * @param abortion the aborter
     * @param args the processor arguments
     * @param intTRSProof an awesome proof to be built
     */
    public RuleAnalyzer(final PolynomialOrderArguments args,
            final Set<IGeneralizedRule> intTRSRules,
            final FormulaFactory<SMTLIBTheoryAtom> formulaFactory,
            final FreshNameGenerator gen, final Abortion abortion,
            final IntTRSPoloRedPairProof intTRSProof) {
        this.rules = intTRSRules;
        this.aborter = abortion;
        this.symbols = new LinkedHashSet<FunctionSymbol>(this.rules.size());
        this.upperBounds = new LinkedHashMap<String, BigInteger>();
        this.lowerBounds = new LinkedHashMap<String, BigInteger>();
        this.factory = formulaFactory;
        this.boundHeuristic = new LinkedHashMap<>();
        this.arguments = args;
        this.proof = intTRSProof;
        this.ng = gen;
    }

    /**
     * Tries to find a polynomial interpretation which automatically yields a
     * polynomial order [a term order]. If this succeeds, then we will return a
     * smaller set of rules.
     * @return list of set of rules
     * @throws AbortionException can be aborted
     */
    public LinkedList<Set<IGeneralizedRule>> analyze() throws AbortionException {
        // Already done?
        if (this.resultSystems != null) {
            return this.resultSystems;
        }

        // Lets go!
        this.buildIndefiniteInterpretation();
        this.buildRulePolynomials();
        this.aborter.checkAbortion();
        this.buildArgumentConstraints();
        this.findBounds();
        this.aborter.checkAbortion();
        this.inferCoefficientConstraints();
        this.aborter.checkAbortion();
        this.findCoefficients();
        this.createResult();

        // YAY!
        return this.resultSystems;
    }

    /**
     * Writes the answer in the heuristic map.
     * @param varName current variable
     * @param increasing used in a increasing way
     * @param decreasing used in a decreasing way
     */
    private void updateHeuristic(final String varName,
        final boolean increasing,
        final boolean decreasing) {
        if (increasing && !decreasing) {
            this.boundHeuristic.put(varName, BoundUsage.USE_UPPER_BOUND);
        } else if (decreasing && !increasing) {
            this.boundHeuristic.put(varName, BoundUsage.USE_LOWER_BOUND);
        } else {
            switch (this.arguments.boundBehavior) {
            case PREFER_LOWER_BOUNDS:
                this.boundHeuristic.put(varName, BoundUsage.USE_LOWER_BOUND);
                break;
            case PREFER_UPPER_BOUNDS:
                this.boundHeuristic.put(varName, BoundUsage.USE_UPPER_BOUND);
                break;
            default:
                final double number = Math.random();
                this.boundHeuristic.put(varName, number > 0.5
                    ? BoundUsage.USE_LOWER_BOUND : BoundUsage.USE_UPPER_BOUND);
            }
        }
    }

    /**
     * Calculates the bound heuristic. If we only add positive numbers to a
     * variable then, it might be useful to use the upper bound. Similarly when
     * we only subtract something. In case a variable is used in both ways, then
     * we do what the bound behavior argument says.
     * @param iRule the current rule
     */
    private void updateBoundHeuristic(final IGeneralizedRule iRule) {
        for (final TRSVariable var : iRule.getCondTerm().getVariables()) {
            final String varName = var.getName();
            if (!(this.lowerBounds.containsKey(varName) && this.upperBounds.containsKey(varName))) {
                continue;
            }

            boolean addedToPositiveInteger = false;
            boolean addedToNegativeInteger = false;

            for (final TRSTerm argument : ((TRSFunctionApplication) iRule.getRight()).getArguments()) {
                if (argument.getVariables().contains(var)) {
                    final VarPolynomial argumentPoly =
                        ToolBox.intTermToPolynomial(argument, this.ng);
                    if (argumentPoly.getDegree() >= 2) {
                        // Too complicated for this heuristic, so we ignore such terms.
                        continue;
                    }
                    final SimplePolynomial coeffOfVar =
                        argumentPoly.getCoefficientPoly(varName);

                    final BigInteger coeffOfVarValue =
                        coeffOfVar.getNumericalAddend();
                    if (coeffOfVarValue.compareTo(BigInteger.ZERO) <= 0) {
                        // Only use term, where the variable occurs with positive sign:
                        continue;
                    }

                    final LinkedHashMap<String, VarPolynomial> subsitution =
                        new LinkedHashMap<>(1);
                    subsitution.put(varName, VarPolynomial.ZERO);
                    final VarPolynomial filteredPoly =
                        argumentPoly.substituteVariables(subsitution);

                    if (!this.canBeNegative(filteredPoly)) {
                        addedToPositiveInteger = true;
                    }
                    if (!this.canBePositive(filteredPoly)) {
                        addedToNegativeInteger = true;
                    }
                }
            }

            this.updateHeuristic(varName, addedToPositiveInteger,
                addedToNegativeInteger);
        }
    }

    /**
     * Returns true, if the linear polynomial can be made negative.
     * @param poly some polynomial
     * @return boolean
     */
    private boolean canBeNegative(final VarPolynomial poly) {
        final Set<String> variables = poly.getVariables();
        final LinkedHashMap<String, VarPolynomial> boundSub =
            new LinkedHashMap<>(variables.size());
        for (final String var : variables) {
            final SimplePolynomial coeffPoly = poly.getCoefficientPoly(var);
            final BigInteger coeffValue = coeffPoly.getNumericalAddend();

            final LinkedHashMap<String, BigInteger> boundMap;
            if (coeffValue.compareTo(BigInteger.ZERO) > 0) {
                boundMap = this.lowerBounds;
            } else {
                boundMap = this.upperBounds;
            }

            if (boundMap.containsKey(var)) {
                boundSub.put(var, VarPolynomial.create(boundMap.get(var)));
            } else {
                return true;
            }
        }

        final VarPolynomial smallestValuePoly =
            poly.substituteVariables(boundSub);
        final BigInteger smallestValue =
            smallestValuePoly.getConstantPart().getNumericalAddend();

        return smallestValue.compareTo(BigInteger.ZERO) < 0;
    }

    /**
     * Returns true, if the linear polynomial can be made positive.
     * @param poly some polynomial
     * @return boolean
     */
    private boolean canBePositive(final VarPolynomial poly) {
        return this.canBeNegative(poly.negate());
    }

    /**
     * Builds the interpretation. Uses indefinite variables to represent unknown
     * coefficients.
     * @throws AbortionException can be aborted
     */
    private void buildIndefiniteInterpretation() throws AbortionException {
        // 1. Initialize
        this.findSymbols();
        final Map<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>> mapping =
            new LinkedHashMap<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>>(
                this.symbols.size());

        // 2. Create initial mapping
        for (final FunctionSymbol symbol : this.symbols) {
            final int arity = symbol.getArity();
            final ArrayList<String> args = new ArrayList<String>(arity);
            VarPolynomial poly =
                VarPolynomial.createCoefficient(this.ng.getFreshName("d", false));
            for (int i = 0; i < arity; i++) {
                final String arg = this.ng.getFreshName("x", false);
                args.add(arg);
                for (int k = 1; k <= this.arguments.degree; k++) {
                    final String coefficient = this.ng.getFreshName("c", false);
                    poly =
                        poly.plus(VarPolynomial.createCoefficient(coefficient).times(
                            VarPolynomial.createVariable(arg).power(k,
                                this.aborter)));
                }
            }
            if (this.arguments.degree == 2) {
                for (int i = 0; i < arity; i++) {
                    for (int j = i + 1; j < arity; j++) {
                        final String coefficient =
                            this.ng.getFreshName("c", false);
                        poly =
                            poly.plus(VarPolynomial.createVariable(args.get(i)).times(
                                VarPolynomial.createVariable(args.get(j))).times(
                                VarPolynomial.createCoefficient(coefficient)));
                    }
                }
            }
            mapping.put(symbol, new Pair<ArrayList<String>, VarPolynomial>(
                args, poly));
        }

        // 3. Create the interpretation
        this.interpretation = PolynomialInterpretation.create(mapping, this.ng);

        if (Globals.DEBUG_MATTHIAS) {
            DebugLogger.getLogger("poly").logln(
                "Created indefinite interpretation:\n"
                    + this.interpretation.toString());
        }
    }

    /** Find all symbols occurring in the rules. */
    private void findSymbols() {
        for (final IGeneralizedRule iRule : this.rules) {
            final TRSFunctionApplication left = iRule.getLeft();
            final TRSTerm rightTerm = iRule.getRight();
            assert rightTerm instanceof TRSFunctionApplication;
            final TRSFunctionApplication right = (TRSFunctionApplication) rightTerm;

            this.symbols.add(left.getRootSymbol());
            this.symbols.add(right.getRootSymbol());
        }
    }

    /**
     * Builds polynomials: [left]_interpretation - [right]_interpretation and
     * [left]_interpretation
     * @throws AbortionException can be aborted
     */
    private void buildRulePolynomials() throws AbortionException {
        this.diffPolys =
            new LinkedHashMap<IGeneralizedRule, VarPolynomial>(
                this.rules.size());
        this.leftPolys =
            new LinkedHashMap<IGeneralizedRule, VarPolynomial>(
                this.rules.size());

        for (final IGeneralizedRule iRule : this.rules) {
            this.aborter.checkAbortion();
            final TRSFunctionApplication left = iRule.getLeft();
            final TRSFunctionApplication right =
                (TRSFunctionApplication) iRule.getRight();
            this.diffPolys.put(
                iRule,
                this.interpretation.apply(left).minus(
                    this.interpretation.apply(right)));
            this.leftPolys.put(iRule, this.interpretation.apply(left));
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("poly");
            logger.logln("Created some polys:");
            for (final IGeneralizedRule iRule : this.rules) {
                logger.logln("diff( " + iRule + " ) = "
                    + this.diffPolys.get(iRule));
                logger.logln("left( " + iRule + " ) = "
                    + this.leftPolys.get(iRule));
            }
            logger.logln();
        }
    }

    /**
     * Find argument constraints.
     * @throws AbortionException
     */
    private void buildArgumentConstraints() throws AbortionException {
        // At this point we assume, that the constraints are
        // already transformed into disjunction free formulas.
        this.argumentConstraints =
            new LinkedHashMap<IGeneralizedRule, List<PolynomialConstraint>>(
                this.rules.size());

        for (final IGeneralizedRule iRule : this.rules) {
            final TRSTerm cond = iRule.getCondTerm();
            if (!(cond instanceof TRSFunctionApplication)) {
                if (Globals.DEBUG_MATTHIAS) {
                    DebugLogger.getLogger("poly").logln(
                        "PolynomialInterpretationFinder.buildArgumentConstraints(): Condition is variable!");
                    assert false;
                }
                continue;
            }
            List<PolynomialConstraint> polyConds =
                ToolBox.boolTermToPolynomialConstraints(
                    (TRSFunctionApplication) cond, this.ng, this.aborter);

            // only consider linear constraints in certified mode
            boolean linearOnly = !Options.certifier.isNone();
            if (linearOnly) {
                polyConds = polyConds.stream().filter(x -> x.getPolynomial().isLinear()).collect(toList());
            }
            this.argumentConstraints.put(iRule, polyConds);
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("poly");
            logger.logln("Some argument constraints:");
            for (final IGeneralizedRule iRule : this.rules) {
                logger.logln("Constraints( " + iRule + " ):");
                logger.logln(this.argumentConstraints.get(iRule).toString());
            }
            logger.logln();
        }
    }

    /**
     * Transforms argument constraints in order to find bounds.
     * @throws AbortionException can be aborted
     */
    private void findBounds() throws AbortionException {
        this.updateSubstitutionHeuristic();

        for (final IGeneralizedRule iRule : this.rules) {
            final List<PolynomialConstraint> constraints =
                this.argumentConstraints.get(iRule);
            final ArrayList<PolynomialConstraint> complexConstraints =
                new ArrayList<PolynomialConstraint>(constraints.size());
            final LinkedHashSet<String> expressedOrBounded =
                new LinkedHashSet<String>(constraints.size());

            this.findSimpleBounds(constraints, complexConstraints,
                expressedOrBounded);

            if (this.arguments.combineArgumentConstraints) {
                this.combineArgumentConstraints(complexConstraints);
            }

            this.handleComplexArgumentConstraints(iRule, complexConstraints,
                expressedOrBounded);

            this.updateBoundHeuristic(iRule);
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("poly");
            logger.logln("We found the following bounds:");
            logger.logln("Lower bounds:\n" + this.lowerBounds.toString());
            logger.logln("Upper bounds:\n" + this.upperBounds.toString());
            logger.logln();
            logger.logln("We will use the following heuristic for bound usage:");
            logger.logln(this.boundHeuristic.toString());
            logger.logln();
        }
    }

    /**
     * Updates the information needed for the heuristic which has an influence
     * on the decision of the variable to be substituted.
     */
    private void updateSubstitutionHeuristic() {
        this.substitutionAvoidanceSet = new LinkedHashSet<String>();
        final LinkedHashMap<String, LinkedHashSet<SimplePolynomial>> coefficients =
            new LinkedHashMap<String, LinkedHashSet<SimplePolynomial>>();
        for (final VarPolynomial vp : this.leftPolys.values()) {
            this.updateSubstitutionWithPolynomial(coefficients, vp);
        }
        for (final VarPolynomial vp : this.diffPolys.values()) {
            this.updateSubstitutionWithPolynomial(coefficients, vp);
        }
    }

    /**
     * Updates the heuristic with a special polynomial to be read.
     * @param coefficients maps each variable to the leadings coefficients
     * @param vp the current polynomial
     */
    private void updateSubstitutionWithPolynomial(final LinkedHashMap<String, LinkedHashSet<SimplePolynomial>> coefficients,
        final VarPolynomial vp) {
        for (final Entry<IndefinitePart, SimplePolynomial> entry : vp.getVarMonomials().entrySet()) {
            final SimplePolynomial simplePart = entry.getValue();
            final IndefinitePart indefPart = entry.getKey();
            for (final String x : indefPart.getExponents().keySet()) {
                if (!coefficients.containsKey(x)) {
                    coefficients.put(x, new LinkedHashSet<SimplePolynomial>());
                }
                coefficients.get(x).add(simplePart);
                if (coefficients.get(x).contains(simplePart.negate())) {
                    this.substitutionAvoidanceSet.add(x);
                }
            }
        }
    }

    /**
     * Finds simple bounds.
     * @param constraints list of constraints
     * @param complexConstraints list to fill in the complex constraints
     * @param expressedOrBounded set of variables that are bounded or expressed
     */
    private void findSimpleBounds(final List<PolynomialConstraint> constraints,
        final ArrayList<PolynomialConstraint> complexConstraints,
        final LinkedHashSet<String> expressedOrBounded) {
        for (final PolynomialConstraint constraint : constraints) {
            if (constraint.isBound()) {
                this.registerBound(constraint);
                expressedOrBounded.add(constraint.getBoundedVariable());
            } else {
                complexConstraints.add(constraint);
            }
        }
    }

    /**
     * Tries to combine argument constraint.
     * @param constraints an ArrayList of complex constraints
     */
    private void combineArgumentConstraints(final ArrayList<PolynomialConstraint> constraints) {
        final ArrayList<PolynomialConstraint> complexConstraints =
            new ArrayList<PolynomialConstraint>(constraints);
        boolean combined = false;
        do {
            combined = false;
            for (int i = 0; i < complexConstraints.size(); i++) {
                final PolynomialConstraint complex = complexConstraints.get(i);
                combined = combined || this.tryToCombine(complex);
                if (combined) {
                    complexConstraints.remove(i);
                    break;
                }
            }
        } while (combined);
    }

    /**
     * Tries to combine constraints with each other in order to find more
     * bounds.
     * @param constraint current constraint
     * @return true IFF success
     */
    private boolean tryToCombine(final PolynomialConstraint constraint) {
        switch (constraint.getType()) {
        case PCT_GE:
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln();
                logger.logln("Trying to use " + constraint);
            }
            final VarPolynomial vp = constraint.getPolynomial();
            VarPolynomial rewritten = VarPolynomial.ZERO;
            for (final Entry<IndefinitePart, SimplePolynomial> entry : vp.getVarMonomials().entrySet()) {
                rewritten = this.findAndAddUpperBound(rewritten, entry);
            }
            final PolynomialConstraint rewrittenConstraint =
                new PolynomialConstraint(rewritten,
                    PolynomialConstraintType.PCT_GE, this.ng);
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln("Was rewritten to " + rewrittenConstraint);
            }

            if (rewrittenConstraint.isBound()) {
                this.registerBound(rewrittenConstraint);
                return true;
            } else {
                return false;
            }
        case PCT_LE:
            return this.tryToCombine(new PolynomialConstraint(
                constraint.getPolynomial().negate(),
                PolynomialConstraintType.PCT_GE, this.ng));
        case PCT_EQ:
            final boolean b1 =
                this.tryToCombine(new PolynomialConstraint(
                    constraint.getPolynomial(),
                    PolynomialConstraintType.PCT_GE, this.ng));
            final boolean b2 =
                this.tryToCombine(new PolynomialConstraint(
                    constraint.getPolynomial().negate(),
                    PolynomialConstraintType.PCT_GE, this.ng));

            // The results have to stored, because the compiler optimizes evaluation of OR-expressions!
            return b1 || b2;
        default:
            assert false : "Someone added a new type?!";
            return false;
        }
    }

    /**
     * Adds [currentMonomial] or a upper of [currentMonomial] to [toAdd] and
     * returns the result.
     * @param toAdd VarPolynomial to add
     * @param currentMonomial the current monomial
     * @return a VarPolynomial
     */
    private VarPolynomial findAndAddUpperBound(final VarPolynomial toAdd,
        final Entry<IndefinitePart, SimplePolynomial> currentMonomial) {
        VarPolynomial result = toAdd;
        final IndefinitePart indefPart = currentMonomial.getKey();
        final SimplePolynomial simplePart = currentMonomial.getValue();
        final BigInteger coeff = simplePart.getNumericalAddend();
        final String theOneAndOnly = indefPart.getTheOnlyIndefinite();

        if (indefPart.equals(IndefinitePart.ONE)) {
            // Constant will not be touched:
            result = result.plus(VarPolynomial.create(coeff));
        } else if (theOneAndOnly != null) {
            // So our monomial has the form d*y^n
            final Integer exponent = indefPart.getExponent(theOneAndOnly);
            final int comparison = coeff.compareTo(BigInteger.ZERO);

            final BigInteger lowerBound = this.lowerBounds.get(theOneAndOnly);
            final BigInteger upperBound = this.upperBounds.get(theOneAndOnly);

            if (comparison > 0) {
                if (exponent % 2 == 0) {
                    // We have d > 0 and n even!
                    // If we have a lower and upper bound, then
                    // we can create a upper bound of d*y^n.
                    if (lowerBound != null && upperBound != null) {
                        final BigInteger absMax =
                            lowerBound.abs().max(upperBound.abs());
                        result =
                            result.plus(VarPolynomial.create(coeff.multiply(absMax.pow(exponent))));
                    } else {
                        result =
                            result.plus(ToolBox.createVarPolynomial(simplePart,
                                indefPart));
                    }
                } else {
                    // We have d > 0 and n odd!
                    // So a upper bound for y will give a upper bound for d*y^n.
                    if (upperBound != null) {
                        result =
                            result.plus(VarPolynomial.create(coeff.multiply(upperBound.pow(exponent))));
                    } else {
                        result =
                            result.plus(ToolBox.createVarPolynomial(simplePart,
                                indefPart));
                    }
                }
            } else if (comparison < 0) {
                if (exponent % 2 != 0) {
                    // We have d < 0 and n odd!
                    // A lower bound for y will give a upper bound for d*y^n.
                    if (lowerBound != null) {
                        result =
                            result.plus(VarPolynomial.create(coeff.multiply(lowerBound.pow(exponent))));
                    } else {
                        result =
                            result.plus(ToolBox.createVarPolynomial(simplePart,
                                indefPart));
                    }
                }
                // The case d < 0 and n even is not interesting, since then we have d*y^n <= 0.
            }
        } else {
            // Too complex to handle this yet -> just add it again!
            result =
                result.plus(ToolBox.createVarPolynomial(simplePart, indefPart));
        }

        return result;
    }

    /**
     * Handles complex constraints.
     * @param iRule the current rule
     * @param complexConstraints ArrayList of complex constraints to handle
     * @param expressedOrBounded set of variable, that are expressed or bounded
     * @throws AbortionException can be aborted
     */
    private void handleComplexArgumentConstraints(final IGeneralizedRule iRule,
        final ArrayList<PolynomialConstraint> complexConstraints,
        final LinkedHashSet<String> expressedOrBounded)
            throws AbortionException {
        for (int i = 0; i < complexConstraints.size(); i++) {
            final PolynomialConstraint complex = complexConstraints.get(i);
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln("Checking constraint: " + complex);
            }
            final List<String> expressible = complex.getExpressibleVariables();

            if (expressible.isEmpty()) {
                continue;
            }

            // Find a suitable candidate:
            String toExpress = expressible.get(0);
            if (this.arguments.useSubstitutionHeuristic) {
                for (final String candidate : expressible) {
                    if (!this.substitutionAvoidanceSet.contains(candidate)) {
                        toExpress = candidate;
                        break;
                    }
                }
                for (final String candidate : expressible) {
                    if (!expressedOrBounded.contains(candidate)
                        && !this.substitutionAvoidanceSet.contains(candidate)) {
                        toExpress = candidate;
                        break;
                    }
                }
            }
            // TODO: Find a better solution for substitutions!
            // toExpress = expressible.get(0);

            final Pair<VarPolynomial, PolynomialConstraint> pair =
                complex.expressVariable(toExpress);
            final VarPolynomial expression = pair.getKey();

            // Check whether or not this would introduce too many new variables:
            final Set<TRSVariable> variables = iRule.getVariables();
            int newVariables = 0;
            for (final String variableName : expression.getVariables()) {
                final TRSVariable variable = TRSTerm.createVariable(variableName);
                if (!variables.contains(variable)) {
                    newVariables++;
                }
            }
            if (newVariables >= 2) {
                // This would introduce at least 2 new variables. Thus
                // we do not accept this substitution.
                continue;
            }

            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln(complex.toString() + " was rewritten by using "
                    + toExpress + " = " + expression);
                logger.logln("Thus we have " + pair.getValue() + ".");
            }

            this.registerBound(pair.getValue());

            this.substitute(toExpress, expression, iRule);
            expressedOrBounded.add(toExpress);

            // Rewrite constraints we have to visit later:
            for (int j = complexConstraints.size() - 1; j >= i + 1; j--) {
                final PolynomialConstraint toRewrite =
                    complexConstraints.get(j);
                toRewrite.substituteVariable(toExpress, expression);
                if (toRewrite.isBound()) {
                    expressedOrBounded.add(toRewrite.getBoundedVariable());
                    this.registerBound(toRewrite);
                    complexConstraints.remove(j);
                }
            }
        }
    }

    /**
     * Registers a bound.
     * @param bound the bound to register
     */
    private void registerBound(final PolynomialConstraint bound) {
        if (!bound.isBound()) {
            assert false : bound.toString() + " is not a bound!";
            return;
        }

        final String boundedVariable = bound.getBoundedVariable();
        assert (bound.isLowerBound() || bound.isUpperBound())
            && boundedVariable != null;

        // Take the minimal (maximal) upper (lower) bound:
        if (bound.isUpperBound()) {
            if (this.upperBounds.containsKey(boundedVariable)) {
                final BigInteger oldBound =
                    this.upperBounds.get(boundedVariable);
                this.upperBounds.put(boundedVariable,
                    oldBound.min(bound.getUpperBoundValue()));

            } else {
                this.upperBounds.put(boundedVariable,
                    bound.getUpperBoundValue());
            }
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln(bound.toString() + " is a upper bound! Value: "
                    + bound.getUpperBoundValue());
            }
        }
        if (bound.isLowerBound()) {
            if (this.lowerBounds.containsKey(boundedVariable)) {
                final BigInteger oldBound =
                    this.lowerBounds.get(boundedVariable);
                this.lowerBounds.put(boundedVariable,
                    oldBound.max(bound.getLowerBoundValue()));
            } else {
                this.lowerBounds.put(boundedVariable,
                    bound.getLowerBoundValue());
            }
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln(bound.toString() + " is a lower bound! Value: "
                    + bound.getLowerBoundValue());
            }
        }
    }

    /**
     * Substitutes a variable by a polynomial.
     * @param toSubstitute variable to be substituted
     * @param vp polynomial to use
     * @param iRule current rule
     * @throws AbortionException can be aborted
     */
    private void substitute(final String toSubstitute,
        final VarPolynomial vp,
        final IGeneralizedRule iRule) throws AbortionException {
        final LinkedHashMap<String, VarPolynomial> substitution =
            new LinkedHashMap<String, VarPolynomial>(1);
        substitution.put(toSubstitute, vp);

        this.diffPolys.put(
            iRule,
            this.diffPolys.get(iRule).substituteVariables(substitution,
                this.aborter));
        this.leftPolys.put(
            iRule,
            this.leftPolys.get(iRule).substituteVariables(substitution,
                this.aborter));

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("poly");
            logger.logln("Substituted " + toSubstitute + " by " + vp + ".");
            logger.logln("diff( " + iRule + " ) = " + this.diffPolys.get(iRule));
            logger.logln("left( " + iRule + " ) = " + this.leftPolys.get(iRule));
            logger.logln();
        }
    }

    /**
     * Infers coefficient constraints. These constraints can be given to the
     * SMT-Solver in order to find a satisfying assignment, which directly
     * yields the concrete polynomial interpretation.
     * @throws AbortionException can be aborted
     */
    private void inferCoefficientConstraints() throws AbortionException {
        // 1. Initialize
        this.weakCoefficientConstraints =
            new LinkedHashMap<>(this.rules.size());
        this.decreasingCoefficientConstraints =
            new LinkedHashMap<>(this.rules.size());
        this.boundedCoefficientConstraints =
            new LinkedHashMap<>(this.rules.size());

        // 2. Infer constraints:
        for (final IGeneralizedRule iRule : this.rules) {
            final VarPolynomial diffPoly = this.diffPolys.get(iRule);
            final VarPolynomial leftPoly = this.leftPolys.get(iRule);

            // 2.1. Weak constraints:
            final LinkedList<CoefficientConstraint> weakConstraints =
                new LinkedList<CoefficientConstraint>();
            this.inferCoefficientConstraintsForPolynomial(diffPoly,
                weakConstraints);
            this.weakCoefficientConstraints.put(iRule, weakConstraints);

            // 2.2. Deceasing constraints:
            final LinkedList<CoefficientConstraint> decreasingConstraints =
                new LinkedList<CoefficientConstraint>();
            this.inferCoefficientConstraintsForPolynomial(
                diffPoly.minus(VarPolynomial.ONE), decreasingConstraints);

            // 2.3. Bound constraints:
            final LinkedList<CoefficientConstraint> boundedConstraints =
                new LinkedList<CoefficientConstraint>();
            this.inferCoefficientConstraintsForPolynomial(leftPoly,
                boundedConstraints);

            if (this.arguments.useGeneralizedReductionPairs) {
                this.decreasingCoefficientConstraints.put(iRule,
                    decreasingConstraints);
                this.boundedCoefficientConstraints.put(iRule,
                    boundedConstraints);
            } else {
                decreasingConstraints.addAll(boundedConstraints);
                this.decreasingCoefficientConstraints.put(iRule,
                    decreasingConstraints);
            }
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("poly");
            logger.logln("Inferred coefficient constraints:");
            for (final IGeneralizedRule iRule : this.rules) {
                logger.logln("current rule = " + iRule.toString());
                logger.logln("diff = " + this.diffPolys.get(iRule));
                logger.logln("left = " + this.leftPolys.get(iRule));
                if (this.arguments.useGeneralizedReductionPairs) {
                    logger.logln("bounded = "
                        + this.boundedCoefficientConstraints.get(iRule).toString());
                }
                logger.logln("decreasing = "
                    + this.decreasingCoefficientConstraints.get(iRule).toString());
                logger.logln("weak = "
                    + this.weakCoefficientConstraints.get(iRule).toString());
                logger.logln();
            }
        }
    }

    /**
     * Infers some coefficient constraints that will imply the fact, that the
     * given polynomial is greater then Zero. Of course the surrounding
     * condition that arise from the rules must still hold.
     * @param inputPoly the current polynomial
     * @param constraintList list to insert the constraints
     * @throws AbortionException can be aborted
     */
    private void inferCoefficientConstraintsForPolynomial(final VarPolynomial inputPoly,
        final LinkedList<CoefficientConstraint> constraintList)
            throws AbortionException {
        LinkedHashSet<VarPolynomial> realInputPolys = new LinkedHashSet<>();
        realInputPolys.add(inputPoly);

        for (final String x : inputPoly.getVariables()) {
            final BigInteger lower = this.lowerBounds.get(x);
            final BigInteger upper = this.upperBounds.get(x);

            if (lower == null || upper == null) {
                continue;
            }

            // |{x integer | a <= x <= b }| = max(0, b - a + 1)
            final BigInteger intervalSize =
                upper.subtract(lower).add(BigInteger.ONE);

            if (intervalSize.compareTo(BigInteger.ZERO) <= 0) {
                // b - a + 1 <= 0 -> empty -> nothing to do!
                return;
            }

            if (intervalSize.compareTo(BigInteger.valueOf(this.arguments.variableInstantiationLimit)) <= 0) {
                final LinkedHashSet<VarPolynomial> newRealInputPolys =
                    new LinkedHashSet<>();

                for (int i = 0; i < intervalSize.intValue(); i++) {
                    final LinkedHashMap<String, VarPolynomial> substitution =
                        new LinkedHashMap<>(1);
                    substitution.put(x,
                        VarPolynomial.create(lower.add(BigInteger.valueOf(i))));
                    for (final VarPolynomial poly : realInputPolys) {
                        newRealInputPolys.add(poly.substituteVariables(substitution));
                    }
                }
                realInputPolys = newRealInputPolys;
            }
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("poly");
            logger.logln("Watch out for :");
            for (final VarPolynomial realInputPoly : realInputPolys) {
                logger.logln(realInputPoly);
            }
        }

        for (final VarPolynomial realInputPoly : realInputPolys) {
            this.requireGEZero(realInputPoly, constraintList);
        }
    }

    /**
     * Infers constraints ensuring that [poly] >= 0 is valid (using
     * integer-arithmetic).
     * @param inputPoly the polynomial that has to be greater/equals zero
     * @param constraintList list to fill in the inferred constraints
     * @throws AbortionException can be aborted
     */
    private void requireGEZeroAlternative(final VarPolynomial inputPoly,
        final LinkedList<CoefficientConstraint> constraintList)
            throws AbortionException {
        if (inputPoly.getDegree() > 2
            && this.arguments.useNewConstraintsGeneration) {
            // If the new approach is not applicable, then
            // we use the old one.
            this.requireGEZero(inputPoly, constraintList);
            return;
        }

        // 1. Switch to the correct domains (i.e. ensures that variables
        //    ranges over natural numbers)
        final ArrayList<String> variables =
            new ArrayList<>(inputPoly.getVariables());
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("poly");
            l.logln("Try to handle " + inputPoly);
            l.logln("Variables = " + variables);
        }

        // In order to correct the domains, we either
        // enforce the corresponding coefficient to be zero or
        // we make use of the bounds given by the condition.
        final LinkedHashMap<String, VarPolynomial> substitution =
            new LinkedHashMap<>();
        for (final String var : variables) {
            if (!this.lowerBounds.containsKey(var)
                && !this.upperBounds.containsKey(var)) {
                this.removeVariable(var, inputPoly, constraintList,
                    substitution);
            } else {
                this.moveVariableToNats(var, substitution);
            }
        }
        this.aborter.checkAbortion();

        final VarPolynomial natPolynomial =
            inputPoly.substituteVariables(substitution);
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("poly");
            l.logln("Substitution: " + substitution);
            l.logln("NatPoly: " + natPolynomial);
        }

        // 2. Generate the constraints:
        this.generateConstraints(constraintList, variables, natPolynomial);
    }

    /**
     * Uses the converted polynomial (here converted means that the occurring
     * variables range over natural numbers) to generate the constraints.
     * @param constraintList some list to fill in constraints
     * @param variables some variables we are using.
     * @param natPolynomial the converted polynomial
     */
    private void generateConstraints(final LinkedList<CoefficientConstraint> constraintList,
        final ArrayList<String> variables,
        final VarPolynomial natPolynomial) {
        // Require constant part >= 0:
        final CoefficientConstraint constantConstraint =
            new CoefficientConstraint(natPolynomial.getConstantPart(),
                CoefficientConstraintType.GE_ZERO);
        constraintList.add(constantConstraint);
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("poly");
            l.logln("Added " + constantConstraint);
        }

        for (int i = 0; i < variables.size(); i++) {
            for (int j = i; j < variables.size(); j++) {
                final String x = variables.get(i);
                final String y = variables.get(j);

                final IndefinitePart indexIndef =
                    IndefinitePart.create(x, 1).times(
                        IndefinitePart.create(y, 1));

                final SimplePolynomial simple =
                    natPolynomial.getVarMonomials().get(indexIndef);

                if (simple != null) {
                    final CoefficientConstraint constraint =
                        new CoefficientConstraint(simple,
                            CoefficientConstraintType.GE_ZERO);
                    constraintList.add(constraint);
                    if (Globals.DEBUG_MATTHIAS) {
                        final DebugLogger l = DebugLogger.getLogger("poly");
                        l.logln("Added " + constraint);
                    }
                }
            }
        }

        for (final String v : variables) {
            final IndefinitePart indexIndef1 = IndefinitePart.create(v, 1);
            final IndefinitePart indexIndef2 = IndefinitePart.create(v, 2);

            SimplePolynomial coeffPoly1 =
                natPolynomial.getVarMonomials().get(indexIndef1);
            SimplePolynomial coeffPoly2 =
                natPolynomial.getVarMonomials().get(indexIndef2);

            if (coeffPoly1 == null && coeffPoly2 == null) {
                continue;
            }

            coeffPoly1 =
                coeffPoly1 == null ? SimplePolynomial.ZERO : coeffPoly1;
            coeffPoly2 =
                coeffPoly2 == null ? SimplePolynomial.ZERO : coeffPoly2;

            final CoefficientConstraint constraint =
                new CoefficientConstraint(coeffPoly1.plus(coeffPoly2),
                    CoefficientConstraintType.GE_ZERO);
            constraintList.add(constraint);
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger l = DebugLogger.getLogger("poly");
                l.logln("Added " + constraint);
            }
        }
    }

    /**
     * Calculates a sound substitution s.t. the given variable can be assumed to
     * range over the domain of natural numbers.
     * @param var some variable
     * @param substitution substitution to be calculated
     */
    private void moveVariableToNats(final String var,
        final LinkedHashMap<String, VarPolynomial> substitution) {

        final BoundUsage bu;

        if (!this.lowerBounds.containsKey(var)) {
            bu = BoundUsage.USE_UPPER_BOUND;
        } else if (!this.upperBounds.containsKey(var)) {
            bu = BoundUsage.USE_LOWER_BOUND;
        } else {
            assert this.lowerBounds.containsKey(var)
                && this.upperBounds.containsKey(var);
            if (this.useUpperBound(var)) {
                bu = BoundUsage.USE_UPPER_BOUND;
            } else {
                bu = BoundUsage.USE_LOWER_BOUND;
            }
        }
        assert bu != null;

        if (bu == BoundUsage.USE_LOWER_BOUND) {
            substitution.put(
                var,
                VarPolynomial.createVariable(var).plus(
                    VarPolynomial.create(this.lowerBounds.get(var))));
        } else {
            substitution.put(
                var,
                VarPolynomial.create(this.upperBounds.get(var)).minus(
                    VarPolynomial.createVariable(var)));
        }
    }

    /**
     * This forces the coefficient of an unbounded variable to be zero.
     * @param toBeRemoved variable to be eliminated
     * @param inputPoly the input polynomial
     * @param constraintList list of constraint to generate
     * @param substitution substitution to be computed
     */
    private void removeVariable(final String toBeRemoved,
        final VarPolynomial inputPoly,
        final LinkedList<CoefficientConstraint> constraintList,
        final LinkedHashMap<String, VarPolynomial> substitution) {
        final VarPolynomial toSubtract;

        for (final Entry<IndefinitePart, SimplePolynomial> e : inputPoly.getVarMonomials().entrySet()) {
            if (e.getKey().contains(toBeRemoved)) {
                final CoefficientConstraint constraint =
                    new CoefficientConstraint(e.getValue(),
                        CoefficientConstraintType.EQ_ZERO);
                constraintList.add(constraint);
                if (Globals.DEBUG_MATTHIAS) {
                    final DebugLogger l = DebugLogger.getLogger("poly");
                    l.logln("Added " + constraint);
                }
            }
        }

        substitution.put(toBeRemoved, VarPolynomial.ZERO);
    }

    // TEST! //

    /**
     * Infers constraints ensuring that [poly] >= 0 is valid (using
     * integer-arithmetic).
     * @param inputPoly the polynomial that has to be greater/equals zero
     * @param constraintList list to fill in the inferred constraints
     * @throws AbortionException can be aborted
     */
    private void requireGEZero(final VarPolynomial inputPoly,
        final LinkedList<CoefficientConstraint> constraintList)
            throws AbortionException {
        VarPolynomial poly = inputPoly;
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("poly");
            l.logln("requireGEZero: " + poly);
        }

        // 0. Is our long search over?
        if (poly.isConstant()) {
            final SimplePolynomial constantPart = poly.getConstantPart();
            if (constantPart != null) {
                constraintList.add(new CoefficientConstraint(constantPart,
                    CoefficientConstraintType.GE_ZERO));
            }
            return;
        }

        // 1. Hunt for binomial parts:
        poly = this.applySimplifications(constraintList, poly);
        final ImmutableMap<IndefinitePart, SimplePolynomial> varMonomials =
            poly.getVarMonomials();

        // 2. Pick monomial:
        final IndefinitePart picked = ToolBox.getStrongestMonomial(poly);
        if (picked == null) {
            // [poly] is ZERO; thus there is nothing to require.
            return;
        }

        // 3. Investigate exponents:
        final ImmutableMap<String, Integer> exponents = picked.getExponents();
        boolean requireCoefficientEqualsZero = false;
        for (final Entry<String, Integer> entry : exponents.entrySet()) {
            final String x = entry.getKey();
            final Integer exponent = entry.getValue();
            if (exponent % 2 != 0) {
                // Is every variable occurring at odd power bounded?
                if (!this.isBoundedVariable(x)) {
                    // If this is not the case, then we require the coefficient to be zero.
                    requireCoefficientEqualsZero = true;
                    break;
                }
            }
        }

        // 4. Create constraint and solve the rest recursively:
        SimplePolynomial coeff = varMonomials.get(picked);
        if (requireCoefficientEqualsZero) {
            // 3.a) We cannot guarantee that the monomial is bounded,
            // so we require the coefficient to be ZERO.
            constraintList.add(new CoefficientConstraint(coeff,
                CoefficientConstraintType.EQ_ZERO));
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger l = DebugLogger.getLogger("poly");
                l.logln("Adding " + coeff + " = 0");
            }
            this.requireGEZero(
                poly.minus(ToolBox.createVarPolynomial(coeff, picked)),
                constraintList);
        } else {
            // 3.b) The monomial is bounded, so we can subtract
            // the smallest positive polynomial we can build to
            // simplify the problem. Then we continue recursively.
            VarPolynomial toSubtract = VarPolynomial.ONE;
            boolean negate = false;
            for (final Entry<String, Integer> entry : exponents.entrySet()) {
                final String x = entry.getKey();
                final Integer exponent = entry.getValue();
                if (exponent % 2 == 0) {
                    BigInteger c;
                    if (this.lowerBounds.containsKey(x)
                        && this.upperBounds.containsKey(x)) {
                        c =
                            this.lowerBounds.get(x).add(this.upperBounds.get(x)).divide(
                                BigInteger.valueOf(2));
                    } else if (this.lowerBounds.containsKey(x)) {
                        c = this.lowerBounds.get(x);
                    } else if (this.upperBounds.containsKey(x)) {
                        c = this.upperBounds.get(x);
                    } else {
                        c = BigInteger.ZERO;
                    }

                    // Variables occurring at even power can not be negative.
                    toSubtract =
                        toSubtract.times(VarPolynomial.createVariable(x).minus(
                            VarPolynomial.create(c)).power(exponent,
                            this.aborter));
                } else {
                    // If we have a variable occurring at odd power we use
                    // the upper or lower bound to simplify the problem.
                    // Please note that for every n > 0 and every m that
                    // x^n - (x - m)^n is a polynomial with degree < n.
                    final BigInteger bound;
                    final boolean useUpperBound;
                    if (this.lowerBounds.containsKey(x)
                        && this.upperBounds.containsKey(x)) {
                        useUpperBound = this.useUpperBound(x);
                    } else if (this.lowerBounds.containsKey(x)) {
                        useUpperBound = false;
                    } else {
                        useUpperBound = true;
                    }

                    if (useUpperBound) {
                        bound = this.upperBounds.get(x);
                        // Since we want to guarantee that we subtract a positive polynomial
                        // we require the coefficient to have the right sign.
                        negate = !negate;
                    } else {
                        bound = this.lowerBounds.get(x);
                    }

                    final VarPolynomial vp =
                        VarPolynomial.createVariable(x).minus(
                            VarPolynomial.create(bound));
                    toSubtract =
                        toSubtract.times(vp.power(exponent, this.aborter));
                }
            }
            // The coefficient of the polynomial we are going to subtract must equal the coefficient of
            // the picked monomial. Thus we finish building [toSubtract] before negating [coeff].
            toSubtract = toSubtract.times(coeff);
            coeff = negate ? coeff.negate() : coeff;
            constraintList.add(new CoefficientConstraint(coeff,
                CoefficientConstraintType.GE_ZERO));
            // Since we know that the number of monomials with maximal degree will decrease,
            // we can conclude termination.
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger l = DebugLogger.getLogger("poly");
                l.logln("toSubtract = " + toSubtract);
                l.logln("Adding " + coeff + " >= 0");
            }
            this.requireGEZeroAlternative(poly.minus(toSubtract),
                constraintList);
        }
    }

    /**
     * Applies several polynomial simplifications.
     * @param constraintList list of constraints to be completed
     * @param polyomial current polynomial
     * @return simplified polynomial
     * @throws AbortionException can be aborted
     */
    private VarPolynomial applySimplifications(final LinkedList<CoefficientConstraint> constraintList,
        final VarPolynomial polyomial) throws AbortionException {
        VarPolynomial poly = polyomial;
        if (this.arguments.factorBinomials) {
            poly = this.huntForBinomials(poly, constraintList);
        }
        return poly;
    }

    /**
     * Decides whether the upper or the lower bound should be used.
     * @param var name of the variable
     * @return boolean
     */
    private boolean useUpperBound(final String var) {
        if (this.boundHeuristic.containsKey(var)
            && this.arguments.useBoundHeuristic) {
            switch (this.boundHeuristic.get(var)) {
            case USE_UPPER_BOUND:
                return true;
            case USE_LOWER_BOUND:
                return false;
            default:
                break;
            }
        }

        switch (this.arguments.boundBehavior) {
        case PREFER_LOWER_BOUNDS:
            return false;
        case PREFER_UPPER_BOUNDS:
            return true;
        case PREFER_RANDOM_BOUNDS:
            final double number = Math.random();
            return number > 0.5;
        default:
            assert false : "Bad strategy option!";
            return true;
        }
    }

    /**
     * Hunts for binomials and removes them. More formally: It turns sum from i
     * = 0 to 2n of binomial(2n, i) * l * a^i * b^(k - i) (#) into l * (a +
     * b)^(2n). Thus we only require l >= 0 to deduce (#) >= 0.
     * @param inputPoly a VarPolynomial
     * @param constraintList list of constraints to be completed
     * @return simplified polynomial in form of a VarPolynomial
     * @throws AbortionException can be aborted
     */
    private VarPolynomial huntForBinomials(final VarPolynomial inputPoly,
        final LinkedList<CoefficientConstraint> constraintList)
            throws AbortionException {
        VarPolynomial poly = inputPoly;
        final Set<String> variables = poly.getVariables();

        // 1. Repeat until we do not find binomials anymore:
        final boolean found = false;
        do {
            // Pick variables:
            for (final String a : variables) {
                for (final String b : variables) {
                    // Variables should be different!
                    if (a.equals(b)) {
                        continue;
                    }
                    // Pick degree
                    for (int k = 2; k <= this.arguments.degree; k += 2) {
                        // Try to find (a - b)^(k):
                        VarPolynomial coefficient =
                            this.checkBinomial(a, b, true, k, poly);
                        if (coefficient != null) {
                            // If this is possible, then we can remove that binomial.
                            final VarPolynomial subtrahend =
                                VarPolynomial.createVariable(a).minus(
                                    VarPolynomial.createVariable(b)).power(k,
                                    this.aborter).times(coefficient);
                            if (Globals.DEBUG_MATTHIAS) {
                                final DebugLogger l =
                                    DebugLogger.getLogger("poly");
                                l.logln("Found binomial: " + subtrahend
                                    + "\nin " + poly);
                                l.logln("This can be removed, if we require "
                                    + coefficient + " >= 0");
                            }
                            poly = poly.minus(subtrahend);
                            // The only requirement is that the leading coefficient should be >= 0:
                            this.requireGEZero(coefficient, constraintList);
                        } else {
                            // Analogous: Try to find (a + b)^(k):
                            coefficient =
                                this.checkBinomial(a, b, false, k, poly);
                            if (coefficient != null) {
                                final VarPolynomial subtrahend =
                                    VarPolynomial.createVariable(a).plus(
                                        VarPolynomial.createVariable(b)).power(
                                        k, this.aborter).times(coefficient);
                                if (Globals.DEBUG_MATTHIAS) {
                                    final DebugLogger l =
                                        DebugLogger.getLogger("poly");
                                    l.logln("Found binomial: " + subtrahend
                                        + "\nin " + poly);
                                    l.logln("This can be removed, if we require "
                                        + coefficient + " >= 0");
                                }
                                poly = poly.minus(subtrahend);
                                this.requireGEZero(coefficient, constraintList);
                            }
                        }
                    }
                }
            }
        } while (found);

        return poly;
    }

    /**
     * Checks whether or not there is a binomial. If yes, then the leading
     * coefficient is returned. Otherwise we return null.
     * @param a first variable in form of a string
     * @param b second variable
     * @param subtract true for negating b
     * @param k the current degree
     * @param poly the current polynomial
     * @return the leading coefficient, if the binomial occurs. null otherwise.
     */
    private VarPolynomial checkBinomial(final String a,
        final String b,
        final boolean subtract,
        final int k,
        final VarPolynomial poly) {
        // 0. Initialize:
        final ArrayList<LinkedList<Triple<BigInteger, IndefinitePart, IndefinitePart>>> candidateLists =
            new ArrayList<LinkedList<Triple<BigInteger, IndefinitePart, IndefinitePart>>>(
                k + 1);
        for (int i = 0; i <= k; i++) {
            candidateLists.add(new LinkedList<Triple<BigInteger, IndefinitePart, IndefinitePart>>());
        }

        // 1. Find interesting parts of the polynomial:
        // Intuitively we just eliminate the - in this case annoying - brackets!
        for (final Entry<IndefinitePart, SimplePolynomial> entry : poly.getVarMonomials().entrySet()) {
            final IndefinitePart indef = entry.getKey();
            final int expb = indef.getExponent(b);
            if (expb > k) {
                continue;
            }
            if (indef.getExponent(a) == k - expb) {
                final SimplePolynomial simplePart = entry.getValue();
                final ImmutableMap<IndefinitePart, BigInteger> simpleMonomials =
                    simplePart.getSimpleMonomials();
                for (final Entry<IndefinitePart, BigInteger> simpleMonom : simpleMonomials.entrySet()) {
                    candidateLists.get(expb).add(
                        new Triple<BigInteger, IndefinitePart, IndefinitePart>(
                            simpleMonom.getValue(), simpleMonom.getKey(), indef));
                }
            }
        }

        // 2. Try to recognize a leading coefficient, if possible:
        for (final Triple<BigInteger, IndefinitePart, IndefinitePart> first : candidateLists.get(0)) {
            BigInteger number = first.x;
            final IndefinitePart coeffCandy = first.y;
            final IndefinitePart indefPart = first.z;

            // Generate possible leading coefficient pair,
            // i.e. a pair consisting of a part of the
            // simple polynomial (in form of a indefinite part)
            // and the correct IndefinitePart:
            final Pair<IndefinitePart, IndefinitePart> coeffPair =
                new Pair<IndefinitePart, IndefinitePart>(coeffCandy,
                    indefPart.divide(IndefinitePart.create(a, k)));

            boolean isOK = true;
            for (int i = 1; i <= k; i++) {
                // Lets see if we can find something useful:
                final LinkedList<Triple<BigInteger, IndefinitePart, IndefinitePart>> currentCandidates =
                    candidateLists.get(i);
                boolean foundSomething = false;

                for (final Triple<BigInteger, IndefinitePart, IndefinitePart> currentCandidate : currentCandidates) {
                    final BigInteger currentCoeffNumber = currentCandidate.x;
                    final IndefinitePart currentCoeffCandy = currentCandidate.y;
                    final IndefinitePart currentIndefPart = currentCandidate.z;

                    BigInteger currentFactor =
                        ToolBox.calculateBinomialCoefficient(k, i).multiply(
                            BigInteger.valueOf(number.signum()));
                    if (i % 2 != 0 && subtract) {
                        currentFactor = currentFactor.negate();
                    }

                    if (currentFactor.signum() != currentCoeffNumber.signum()
                        || currentFactor.abs().compareTo(
                            currentCoeffNumber.abs()) < 0) {
                        continue;
                    }

                    final Pair<IndefinitePart, IndefinitePart> currentPair =
                        new Pair<IndefinitePart, IndefinitePart>(
                            currentCoeffCandy,
                            currentIndefPart.divide(ToolBox.createIndefinitePart(
                                a, k - i, b, i)));

                    if (currentPair.equals(coeffPair)) {
                        foundSomething = true;
                        number =
                            number.min(currentCoeffNumber.divide(currentFactor));
                    }
                }

                if (!foundSomething) {
                    isOK = false;
                    break;
                }
            }
            if (isOK) {
                final VarPolynomial result =
                    ToolBox.createVarPolynomial(
                        SimplePolynomial.create(coeffPair.x, number),
                        coeffPair.y);
                return result;
            }
        }

        return null;
    }

    /**
     * Return true IFF the given variable is bounded by some argument
     * constraint.
     * @param var given variable (a string)
     * @return boolean
     */
    private boolean isBoundedVariable(final String var) {
        return this.lowerBounds.containsKey(var)
            || this.upperBounds.containsKey(var);
    }

    /**
     * Rewrites the inferred constraints to a SMTFormula.
     * @return list of formulas to satisfy
     */
    private LinkedList<Formula<SMTLIBTheoryAtom>> buildSMTFormulas() {
        // 1. Build weak part:
        final LinkedList<Formula<SMTLIBTheoryAtom>> formulas =
            new LinkedList<Formula<SMTLIBTheoryAtom>>();
        for (final IGeneralizedRule iRule : this.rules) {
            final LinkedList<CoefficientConstraint> weakConstraints =
                this.weakCoefficientConstraints.get(iRule);
            for (final CoefficientConstraint weakConstraint : weakConstraints) {
                formulas.add(this.factory.buildTheoryAtom(weakConstraint.toSMTLIBIntTheoryAtom()));
            }
        }

        // 2. Build strict part:
        final LinkedList<Formula<SMTLIBTheoryAtom>> stricts =
            new LinkedList<Formula<SMTLIBTheoryAtom>>();
        for (final IGeneralizedRule iRule : this.rules) {
            final LinkedList<CoefficientConstraint> strictConstraints =
                this.decreasingCoefficientConstraints.get(iRule);
            final LinkedList<SMTLIBTheoryAtom> rewrittenConstraints =
                this.rewriteListOfCCToAtoms(strictConstraints);
            stricts.add(this.factory.buildAnd(this.factory.buildTheoryAtoms(rewrittenConstraints)));
        }
        formulas.add(this.factory.buildOr(stricts));

        // 3. Build bound formulae (if we use the generalized reductions pairs)
        if (this.arguments.useGeneralizedReductionPairs) {
            final LinkedList<Formula<SMTLIBTheoryAtom>> bounds =
                new LinkedList<>();
            for (final IGeneralizedRule iRule : this.rules) {
                final LinkedList<CoefficientConstraint> boundConstraints =
                    this.boundedCoefficientConstraints.get(iRule);
                final LinkedList<SMTLIBTheoryAtom> rewrittenConstraints =
                    this.rewriteListOfCCToAtoms(boundConstraints);
                bounds.add(this.factory.buildAnd(this.factory.buildTheoryAtoms(rewrittenConstraints)));
            }
            formulas.add(this.factory.buildOr(bounds));
        }

        return formulas;
    }

    /**
     * Rewrites a list of coefficients constraints into a list of
     * SMTLIBTheoryAtoms (int).
     * @param coeffConstraintList some list of coefficient constraints
     * @return some converted atoms
     */
    private LinkedList<SMTLIBTheoryAtom> rewriteListOfCCToAtoms(final LinkedList<CoefficientConstraint> coeffConstraintList) {
        final LinkedList<SMTLIBTheoryAtom> result = new LinkedList<>();
        for (final CoefficientConstraint cc : coeffConstraintList) {
            result.add(cc.toSMTLIBIntTheoryAtom());
        }
        return result;
    }

    /**
     * Tries to find coefficients satisfying the coefficient constraints. If
     * this succeeds, then we can remove at least one rule.
     * @throws AbortionException can be aborted
     */
    private void findCoefficients() throws AbortionException {
        // 1. Build SMT-Formulas:
        final List<Formula<SMTLIBTheoryAtom>> formulas =
            this.buildSMTFormulas();
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("poly");
            logger.logln("Some SMT-Formulas:");
            logger.logln(formulas.toString());
            logger.logln();
        }

        // 2. Solve formulas:
        Pair<YNM, Map<String, String>> answer;
        try {
            answer =
                ToolBox.SMT_ENGINE.solve(formulas, SMTLogic.QF_LIA,
                    this.aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            answer = new Pair<>(YNM.MAYBE, null);
        }
        if (answer == null) {
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln("The SMT solver could not solve it! (null)");
                logger.logln();
            }
            return;
        }
        if (answer.getKey().equals(YNM.YES)) {
            final Set<Entry<String, String>> assignments =
                answer.getValue().entrySet();
            this.model = new LinkedHashMap<String, BigInteger>();
            for (final Entry<String, String> assignment : assignments) {
                this.model.put(assignment.getKey(),
                    new BigInteger(assignment.getValue()));
            }
            this.interpretation.specialize(this.model);

            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln("The SMT solver gave the following solution:");
                logger.logln(this.model.toString());
                logger.logln();
            }
        } else {
            this.interpretation = null;
            if (Globals.DEBUG_MATTHIAS) {
                final DebugLogger logger = DebugLogger.getLogger("poly");
                logger.logln("The SMT solver could not solve it! ("
                    + answer.getKey() + ")");
                logger.logln();
            }
        }
    }

    /**
     * Decides which rules can be removed.
     */
    private void createResult() {
        this.resultSystems = new LinkedList<>();
        if (this.model == null) {
            this.resultSystems.add(this.rules);
        } else {
            // If we have found a model, then we can calculate the rules
            // that can be dropped due to it decrease behavior and due to boundedness.

            final LinkedHashSet<IGeneralizedRule> removedDecreasingRules =
                new LinkedHashSet<IGeneralizedRule>(this.rules.size() - 1);
            final LinkedHashSet<IGeneralizedRule> removedBoundedRules =
                new LinkedHashSet<IGeneralizedRule>(this.rules.size() - 1);

            final LinkedList<IGeneralizedRule> droppedRulesDueToDecrease =
                new LinkedList<IGeneralizedRule>();
            final LinkedList<IGeneralizedRule> droppedRulesDueToBoundedness =
                new LinkedList<IGeneralizedRule>();

            for (final IGeneralizedRule iRule : this.rules) {
                if (Globals.DEBUG_MATTHIAS) {
                    for (final CoefficientConstraint constraint : this.weakCoefficientConstraints.get(iRule)) {
                        assert constraint.isSatisfied(this.model) : "Weak constraint have to be satisfied!";
                    }
                }
                // Can we drop the rule, because it is decreasing?
                final boolean canBeDroppedDueToDecreasing =
                    this.modelSatisfiesAllFormulas(this.decreasingCoefficientConstraints.get(iRule));

                if (!canBeDroppedDueToDecreasing) {
                    removedDecreasingRules.add(iRule);
                    if (Globals.DEBUG_MATTHIAS) {
                        DebugLogger.getLogger("poly").logln(
                            "Could not drop due to decreasing: " + iRule);
                    }
                } else {
                    if (this.proof != null) {
                        droppedRulesDueToDecrease.add(iRule);
                    }

                    if (Globals.DEBUG_MATTHIAS) {
                        DebugLogger.getLogger("poly").logln(
                            "Dropping due to decreasing: " + iRule);
                    }
                }

                if (this.arguments.useGeneralizedReductionPairs) {
                    // Can we drop the rule, because its interpretation is bounded?
                    final boolean canBeDroppedDueToBoundedness =
                        this.modelSatisfiesAllFormulas(this.boundedCoefficientConstraints.get(iRule));

                    if (!canBeDroppedDueToBoundedness) {
                        removedBoundedRules.add(iRule);
                        if (Globals.DEBUG_MATTHIAS) {
                            DebugLogger.getLogger("poly").logln(
                                "Could not drop due to boundedness: " + iRule);
                        }
                    } else {
                        if (this.proof != null) {
                            droppedRulesDueToBoundedness.add(iRule);
                        }

                        if (Globals.DEBUG_MATTHIAS) {
                            DebugLogger.getLogger("poly").logln(
                                "Dropping due to boundedness: " + iRule);
                        }
                    }
                }
            }

            if (removedDecreasingRules.containsAll(removedBoundedRules)) {
                this.resultSystems.add(removedDecreasingRules);
            } else if (removedBoundedRules.containsAll(removedDecreasingRules)) {
                this.resultSystems.add(removedBoundedRules);
            } else {
                this.resultSystems.add(removedDecreasingRules);
                this.resultSystems.add(removedBoundedRules);
            }

            if (this.proof != null) {
                this.proof.setIntepretation(this.interpretation);
                this.proof.setDroppedRulesDueToDecrease(droppedRulesDueToDecrease);
                if (this.arguments.useGeneralizedReductionPairs) {
                    this.proof.setDroppedRulesDueToBoundedness(droppedRulesDueToBoundedness);
                }
            }
        }
    }

    /**
     * Returns true, if the calculated model satisfies all formulas given in the
     * list.
     * @return boolean
     */
    private boolean modelSatisfiesAllFormulas(final LinkedList<CoefficientConstraint> constraints) {
        for (final CoefficientConstraint constraint : constraints) {
            if (!constraint.isSatisfied(this.model)) {
                return false;
            }
        }
        return true;

    }
}
