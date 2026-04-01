package aprove.verification.oldframework.IntTRS.RankingRedPair;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.RankingRedPair.RankingRedPairProcessor.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A Massager takes some massaging options (currently just the degree
 * for the ranking function). It massages a set of desired term
 * constraints so that a linear ranking function for the massaged
 * term constraints gives rise to a (not necessarily linear) ranking
 * function for the original term constraints.
 *
 * (Currently pretty much hard-wired to instrument the program for
 * quadratic ranking functions without mixed monomials, eliminating
 * non-linear products from the original programs in the process.)
 *
 * TODO massage also the /existing/ conditions (which may already contain
 *      non-linear expressions)
 *
 * @author Carsten Fuhs
 */
public class Massager {

    /**
     * Massager's log, stardate ...
     */
    private static Logger log = Logger.getLogger("aprove.verification.oldframework.IntTRS.RankingRedPair.Massager");

    /**
     * Prefix for the fresh name of the variables introduced by massaging.
     */
    private static final String MASSAGE_VAR_PREFIX = "m";

    /**
     * Prefix for fresh names without any relation to existing names
     */
    private static final String MASSAGE_VAR_PREFIX_ABS = "z";

    /**
     * To be used together with MASSAGE_VAR_PREFIX_ABS.
     */
    private int nameIndex = 0;

    /**
     * Parameter:
     * Do we want to go and linearize /everything/?
     * True:  x^2*y becomes z (fresh)
     * False: x^2*y becomes z*y where z stands for x^2
     */
    private final boolean linearizeAll;

    /**
     * Parameter:
     * Template shape for the ranking function.
     */
    private final Template rankingShape;

    /**
     * Global variable:
     * What polynomial does this new abstraction variable stand for?
     * (TODO For a given term constraint!)
     */
    // private final Map<String, VarPolynomial> newVarToOriginalPoly;

    /**
     * Global variable:
     * Maps the original rules that we care about to rules which have
     * undergone some massaging. This massaging may involve adding
     * further arguments to the function symbols that stand for
     * (abstractions of) certain functions applied to certain arguments.
     */
    private final Map<IGeneralizedRule, IGeneralizedRule> massagedRulesToOriginalRules;

    /**
     * Global variable:
     * Maps the original symbols that we care about to symbols which have
     * arisen in the massaging.
     */
    private final Map<FunctionSymbol, FunctionSymbol> massagedSymsToOriginalSyms;

    /**
     * Global variable:
     * Maps the original symbols that we care about to symbols which have
     * arisen in the massaging.
     */
    private final Map<FunctionSymbol, FunctionSymbol> originalSymsToMassagedSyms;

    /**
     * Global variable:
     * When the time has come, an AbortionException shall be thrown.
     */
    private final Abortion aborter;

    /**
     *
     * @param rankingShape
     * @param linearizeAll
     * @param aborter
     */
    private Massager(final Template rankingShape, final boolean linearizeAll, final Abortion aborter) {
        this.rankingShape = rankingShape;
        this.linearizeAll = linearizeAll;
        this.aborter = aborter;
        this.massagedRulesToOriginalRules = new LinkedHashMap<>();
        this.massagedSymsToOriginalSyms = new LinkedHashMap<>();
        this.originalSymsToMassagedSyms = new LinkedHashMap<>();
        // this.newVarToOriginalPoly = new LinkedHashMap<>();

    }

    /**
     * @param rankingShape  the shape the rules shall have after being massaged
     * @param linearizeAll  linearize 'em all (may or may not get implemented :P)
     * @param aborter  will abort things when the massage is not desired any more
     * @return a massager configured for the given ranking shape
     */
    public static Massager create(final Template rankingShape, final boolean linearizeAll, final Abortion aborter) {
        return new Massager(rankingShape, linearizeAll, aborter);
    }


    /**
     * @param massagee shall be massaged (and be remembered), resulting
     *  in an enriched version of the massagee with enough information
     *  to search for more complex data structures
     * @param fng a source for fresh names
     * @throws AbortionException if the caller does not care about
     *  the result anymore
     */
    public void massage(final IGeneralizedRule massagee,
            final FreshNameGenerator fng) throws AbortionException {

        this.aborter.checkAbortion();
        switch (this.rankingShape) {
        case CLASSIC:
            this.massageClassic(massagee, fng);
            break;
        case QUADRATIC:
            this.massageQuadratic(massagee, fng);
            break;
        case ABS:
            this.massageAbs(massagee, fng);
            break;
        default:
            throw new IllegalStateException("Hitherto unknown Template " + this.rankingShape + ", implement this case!");
        }
    }

    /**
     * Do essentially nothing, but remember that.
     *
     * @param massagee
     * @param fng
     * @return
     */
    private IGeneralizedRule massageClassic(final IGeneralizedRule massagee, final FreshNameGenerator fng) {
        final FunctionSymbol lRoot = massagee.getLeft().getRootSymbol();
        this.massagedSymsToOriginalSyms.put(lRoot, lRoot);
        this.originalSymsToMassagedSyms.put(lRoot, lRoot);
        final FunctionSymbol rRoot = ((TRSFunctionApplication) massagee.getRight()).getRootSymbol();
        this.massagedSymsToOriginalSyms.put(rRoot, rRoot);
        this.originalSymsToMassagedSyms.put(rRoot, rRoot);
        this.massagedRulesToOriginalRules.put(massagee, massagee);
        return massagee;
    }

    /**
     * Massages for quadratic interpretations. So f(x1,...,xn) becomes
     * f(x1,...,xn,x1^2,...,xn^2), which then gets abstracted.
     *
     * @param massagee
     * @param fng
     * @return
     * @throws AbortionException
     */
    private IGeneralizedRule massageQuadratic(final IGeneralizedRule massagee, final FreshNameGenerator fng)
            throws AbortionException {
        /*
         * in:  f(w, x, y)
         *         ->  g(5*x + 3, x + y, u + 1)
         *      | phi
         * out: f(w, x, y, z_ww, z_xx, z_yy)
         *         ->  g(5*x + 3, x + y, u + 1,
         *               25*z_xx + 30*x + 9, z_xx + 2*z_xy + z_yy, z_uu + 2*u + 1)
         *      | phi and z_ww >= 0 and z_ww >= w and z_ww >= -w   // lhs_1 square
         *            and z_xx >= 0 and z_xx >= x and z_xx >= -x   // lhs_2 square
         *            and z_yy >= 0 and z_yy >= y and z_yy >= -y   // lhs_3 square
         *            and z_uu >= 0 and z_uu >= u and z_uu >= -u   // optional strengthening: square of free variable
         *            and 25*z_xx + 30*x + 9 >= 0   and 25*z_xx + 30*x + 9 >= 5*x + 3 and 25*z_xx + 30*x + 9 >= -(5*x + 3)  // rhs_1 square
         *            and z_xx + 2*z_xy + z_yy >= 0 and z_xx + 2*z_xy + z_yy >= x + y and z_xx + 2*z_xy + z_yy >= -(x + y)  // rhs_2 square
         *            and z_uu + 2*u + 1 >= 0       and z_uu + 2*u + 1 >= u + 1       and z_uu + 2*u + 1 >= -(u + 1)        // rhs_3 square
         */

        /* That is:
         * - given: f(\vec{s}) -> g(\vec{t}) | phi
         * - a symbol of n arguments shall have 2*n arguments afterwards
         * - for argument i, the argument i+n is its square
         * - first square the arguments, then eliminate the non-linear
         *   monomials in the resulting squares ("mopping up") and map
         *   the replacement variables to the monomials (for now just
         *   1 level, no iteration)
         * - we know p^2 >= 0, p^2 >= p, p^2 >= -p
         *   for p \in { si^2, tj^2, other_replaced_squares },
         *   add that to the condition
         * - we could also add "p^2 = p*p", for completeness
         *   (so far we don't do it, though).
         */

        // Make sure that the variables in massagee are not accidentally considered fresh
        Set<TRSVariable> variables = massagee.getVariables();
        variables.addAll(massagee.getCondVariables());
        fng.lockHasNames(variables);
        variables = null; // not live anymore

        final TRSFunctionApplication fAppLeft = massagee.getLeft();
        final TRSFunctionApplication fAppRight = (TRSFunctionApplication) massagee.getRight();
        final FunctionSymbol leftRoot = fAppLeft.getRootSymbol();
        final FunctionSymbol rightRoot = fAppRight.getRootSymbol();
        final List<TRSTerm> leftArgs = fAppLeft.getArguments();
        final List<TRSTerm> rightArgs = fAppRight.getArguments();

        // 1. Massage function symbols
        final FunctionSymbol massagedLeftRoot = this.massageSymbol(leftRoot, fng);
        final FunctionSymbol massagedRightRoot = this.massageSymbol(rightRoot, fng);

        // 2. put LHS and RHS arguments together into a list, make them polynomials and square them
        final List<TRSTerm> oldArgs = new ArrayList<>();
        oldArgs.addAll(leftArgs);
        oldArgs.addAll(rightArgs);

        // 3. make them polynomials and square them
        final Pair<ArrayList<VarPolynomial>, ArrayList<VarPolynomial>> oldPolysAndSquares =
            this.toPolysWithSquares(oldArgs, fng);
        this.aborter.checkAbortion();

        // 4. abstraction time -- get them squares out of BOTH the
        // freshly generated squared polys AND the original rhs arguments
        final int leftArity = leftRoot.getArity();
        final Triple<ArrayList<VarPolynomial>, ArrayList<VarPolynomial>, Set<String>> massagedPolysAndSquaresAndSquareVars =
            this.abstractSquares(oldPolysAndSquares.x, oldPolysAndSquares.y, leftArity, fng);
        this.aborter.checkAbortion();

        // 5. now put it all together into a new rule
        final TRSTerm oldCond = massagee.getCondTerm();
        final IGeneralizedRule massagedRule =
            this.polysToRule(massagedPolysAndSquaresAndSquareVars.x, massagedPolysAndSquaresAndSquareVars.y,
                massagedLeftRoot, massagedRightRoot, leftArity, massagedPolysAndSquaresAndSquareVars.z, oldCond);

        this.massagedRulesToOriginalRules.put(massagedRule, massagee);
        if (Massager.log.isLoggable(Level.FINER)) {
            Massager.log.finer("Massaged " + massagee + " to " + massagedRule);
        }
        return massagedRule;
    }

    /**
     *
     * @param massagedLeftRightPolys
     * @param massagedLeftRightSquares
     * @param massagedLeftRoot
     * @param massagedRightRoot
     * @param leftArity
     * @param squareVars
     * @param oldCondition
     * @return the corresponding massaged rule
     */
    private IGeneralizedRule polysToRule(final ArrayList<VarPolynomial> massagedLeftRightPolys,
        final ArrayList<VarPolynomial> massagedLeftRightSquares,
        final FunctionSymbol massagedLeftRoot,
        final FunctionSymbol massagedRightRoot,
        final int leftArity,
        final Set<String> squareVars,
        final TRSTerm oldCondition) {

        // 1. we will know about new conditions!
        final Set<TRSTerm> conditions = new LinkedHashSet<TRSTerm>();
        conditions.add(oldCondition);

        // 2. the arguments for the new lhs and the new rhs!
        final int newLArity = massagedLeftRoot.getArity();
        final int newRArity = massagedRightRoot.getArity();

        ArrayList<TRSTerm> lhsArgs = new ArrayList<TRSTerm>(newLArity);
        for (int i = 0; i < leftArity; ++i) {
            final VarPolynomial poly = massagedLeftRightPolys.get(i);
            final TRSTerm arg = ToolBox.polynomialToIntTerm(poly);
            lhsArgs.add(arg);
        }
        for (int i = 0; i < leftArity; ++i) {
            final VarPolynomial squarePoly = massagedLeftRightSquares.get(i);
            final TRSTerm arg = ToolBox.polynomialToIntTerm(squarePoly);
            lhsArgs.add(arg);
            // arg is a square, put that into conditions
            final TRSTerm argSqrt = lhsArgs.get(i);
            Massager.computeSquareConditions(conditions, arg, argSqrt);
        }

        final int leftRightArity = massagedLeftRightPolys.size();
        ArrayList<TRSTerm> rhsArgs = new ArrayList<TRSTerm>(newRArity);
        if (Globals.useAssertions) {
            assert leftRightArity == massagedLeftRightSquares.size() : leftRightArity + " != "
                + massagedLeftRightSquares.size();
            assert newLArity + newRArity == 2 * leftRightArity;
        }
        for (int i = leftArity; i < leftRightArity; ++i) {
            final VarPolynomial poly = massagedLeftRightPolys.get(i);
            final TRSTerm arg = ToolBox.polynomialToIntTerm(poly);
            rhsArgs.add(arg);
        }
        for (int i = leftArity; i < leftRightArity; ++i) {
            final VarPolynomial squarePoly = massagedLeftRightSquares.get(i);
            final TRSTerm arg = ToolBox.polynomialToIntTerm(squarePoly);
            rhsArgs.add(arg);
            // arg is a square, put that into conditions
            final TRSTerm argSqrt = rhsArgs.get(i - leftArity);
            Massager.computeSquareConditions(conditions, arg, argSqrt);
        }

        final ImmutableArrayList<TRSTerm> immLhsArgs = ImmutableCreator.create(lhsArgs);
        final ImmutableArrayList<TRSTerm> immRhsArgs = ImmutableCreator.create(rhsArgs);
        lhsArgs = null;
        rhsArgs = null;

        // 3. the new lhs and the new rhs!
        final TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(massagedLeftRoot, immLhsArgs);
        final TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(massagedRightRoot, immRhsArgs);

        // 4. complete the new condition!
        // TODO for z = x^2 where x is not an argument of lhs or rhs,
        //      we may want to represent that z >= x and z >= -x;
        //      (for z = x^2*y^2 we know nothing about such /linear/ relations)
        for (final String squareVar : squareVars) {
            Massager.computeSquareConditions(conditions, TRSTerm.createVariable(squareVar), null);
        }

        final TRSTerm newCondition = ToolBox.buildAnd(conditions);
        final IGeneralizedRule res = IGeneralizedRule.create(lhs, rhs, newCondition);
        return res;
    }

    /**
     * @param massagee
     * @param fng
     * @return
     * @throws AbortionException
     */
    private IGeneralizedRule massageAbs(final IGeneralizedRule massagee, final FreshNameGenerator fng)
            throws AbortionException {

        /*
         * in:  f(w, x, y)
         *         ->  g(5*x + 3, x + y, u + 1)
         *      | phi
         * out: f(w, x, y, w_abs, x_abs, y_abs)
         *         ->  g(5*x + 3, x + y, u + 1,
         *               r1_abs, r2_abs, r3_abs)
         *      | phi and w_abs >= 0 and w_abs >= w and w_abs >= -w   // lhs_1
         *            and x_abs >= 0 and x_abs >= x and x_abs >= -x   // lhs_2
         *            and y_abs >= 0 and y_abs >= y and y_abs >= -y   // lhs_3
         *            and r1_abs >= 0 and r1_abs >= 5*x + 3 and r1_abs >= -(5*x + 3) // rhs_1
         *            and r2_abs >= 0 and r2_abs >= x + y   and r2_abs >= -(x + y)   // rhs_2
         *            and r3_abs >= 0 and r3_abs >= u + 1   and r3_abs >= -(u + 1)   // rhs_3
         */

        /*
         * [TODO
         * express |x+3| /as a function of x (or of |x|)/
         * here y = |x| and z = |x+3|
         *
         * in:  f(x) -> g(x+3) | phi
         * out: f(x, y) -> g(x+3, z)     | phi and y >= 0 and y >= x+3 and y >= -(x+3)
         *      f(x, y) -> g(x+3, ...) ]
         */

        /*
         * - given: f(\vec{s}) -> g(\vec{t}) | phi
         * - a symbol of n arguments shall have 2*n arguments afterwards
         * - for argument i, the argument i+n is a fresh variable for its absolute
         * - we know abs_p >= 0, abs_p >= p, abs_p >= -p, add that
         *   to the condition for all introduced fresh variables abs_p
         */

        // * absolute: for abs_x we know:
        //   abs_x >= 0 (bounded!) and abs_x >= x and abs_x >= -x and (x = abs_x or -x = abs_x).
        //     -> the disjunction may become convenient if we want precision,
        //        even at the cost of rule duplication. so far we only do
        //        1-to-1 massaging, so we omit such disjunctive knowledge.
        // * note that we'd need /two/ rules for the latter
        // Make sure that the variables in massagee are not accidentally considered fresh
        Set<TRSVariable> variables = massagee.getVariables();
        variables.addAll(massagee.getCondVariables());
        fng.lockHasNames(variables);
        variables = null; // not live anymore
        final TRSFunctionApplication fAppLeft = massagee.getLeft();
        final TRSFunctionApplication fAppRight = (TRSFunctionApplication) massagee.getRight();
        final FunctionSymbol leftRoot = fAppLeft.getRootSymbol();
        final FunctionSymbol rightRoot = fAppRight.getRootSymbol();
        final List<TRSTerm> leftArgs = fAppLeft.getArguments();
        final List<TRSTerm> rightArgs = fAppRight.getArguments();
        // 1. Massage function symbols
        final FunctionSymbol massagedLeftRoot = this.massageSymbol(leftRoot, fng);
        final FunctionSymbol massagedRightRoot = this.massageSymbol(rightRoot, fng);
        final int leftArity = leftRoot.getArity();
        final int rightArity = rightRoot.getArity();
        this.aborter.checkAbortion();
        // 2. we have f(\vec(x})          -> g(\vec{t})          | phi
        //    we want f'(\vec(x},\vec{y}) -> g'(\vec{t},\vec{z}) | phi AND encodeAbs(yi, xi) AND encodeAbs(zi, ti)
        final TRSTerm oldCond = massagee.getCondTerm();
        final ArrayList<TRSTerm> newConds = new ArrayList<>(1 + 3 * (leftArity + rightArity));
        newConds.add(oldCond);
        final TRSFunctionApplication newRuleLeft = this.computeNewAbsTerm(massagedLeftRoot, leftArgs, newConds, fng);
        final TRSFunctionApplication newRuleRight = this.computeNewAbsTerm(massagedRightRoot, rightArgs, newConds, fng);
        this.aborter.checkAbortion();
        final TRSTerm newCondition = ToolBox.buildAnd(newConds);
        final IGeneralizedRule massagedRule = IGeneralizedRule.create(newRuleLeft, newRuleRight, newCondition);
        this.aborter.checkAbortion();
        this.massagedRulesToOriginalRules.put(massagedRule, massagee);
        if (Massager.log.isLoggable(Level.FINER)) {
            Massager.log.finer("Massaged " + massagee + " to " + massagedRule);
        }
        return massagedRule;
    }

    /**
     * @param newF - f'
     * @param oldArgs - [t1, ..., tn]
     * @param newConds - non-null, will be equipped with further conditions
     *  that connect the fresh new arguments zi and oldArgs
     * @param fng - Fresh! Name! Generator!
     * @return f'(t1, ..., tn, z1, ..., zn)
     */
    private TRSFunctionApplication computeNewAbsTerm(
        final FunctionSymbol newF,
        final List<TRSTerm> oldArgs,
        final List<TRSTerm> newConds,
        final FreshNameGenerator fng
    ) {
        final int newArity = newF.getArity();
        final List<TRSTerm> newArgs = new ArrayList<>(newArity);
        newArgs.addAll(oldArgs);
        final int oldArity = oldArgs.size();
        if (Globals.useAssertions) {
            assert newArity == 2 * oldArity;
        }
        for (int i = 0; i < oldArity; ++i) {
            final String proposalName = this.proposeName();
            final String replacement = fng.getFreshName(proposalName, false);
            final TRSVariable absVar = TRSTerm.createVariable(replacement);
            newArgs.add(absVar);
            final TRSTerm oldArg = oldArgs.get(i);
            Massager.computeAbsConditions(newConds, absVar, oldArg);
        }
        final ImmutableList<TRSTerm> resArgs = ImmutableCreator.create(newArgs);
        final TRSFunctionApplication res = TRSTerm.createFunctionApplication(newF, resArgs);
        return res;
    }

    /**
     * Side effect: The massager will remember oldF and its massaged version,
     * so massaging the same function symbol several times always yields the
     * same output as the first time.
     *
     * @param oldF - we want a function symbol to stand for f in the massaged
     *  term constraints
     * @param fng - fresh! name! generator!
     * @return a massaged version of oldF
     */
    public FunctionSymbol massageSymbol(final FunctionSymbol oldF, final FreshNameGenerator fng) {
        FunctionSymbol newF = this.originalSymsToMassagedSyms.get(oldF);
        if (newF == null) {
            switch (this.rankingShape) {
            case CLASSIC:
                newF = oldF;
                break;
            case QUADRATIC:
            case ABS:
                final String newFName = fng.getFreshName(oldF.getName(), true);
                final int newArity = oldF.getArity() * 2;
                newF = FunctionSymbol.create(newFName, newArity);
                break;
            default:
                throw new IllegalStateException("Unknown ranking shape " + this.rankingShape + "!");
            }
            this.originalSymsToMassagedSyms.put(oldF, newF);
            this.massagedSymsToOriginalSyms.put(newF, oldF);
        }
        return newF;
    }

    /**
     * @param terms [t1, ..., tn] as IDP-style terms
     * @param fng - fresh names!
     * @return [t1, ..., tn] as polynomials
     * @throws AbortionException stops the action when the time has come
     */
    public ArrayList<VarPolynomial> toPolys(final List<TRSTerm> terms, final FreshNameGenerator fng)
            throws AbortionException {
        final int termsSize = terms.size();
        final ArrayList<VarPolynomial> res = new ArrayList<>(termsSize);
        // make the first n polynomials
        for (final TRSTerm t : terms) {
            final VarPolynomial poly = ToolBox.intTermToPolynomial(t, fng);
            res.add(poly);
        }
        this.aborter.checkAbortion();
        return res;
    }

    /**
     * @param terms [t1, ..., tn] as IDP-style terms
     * @param fng - fresh names!
     * @return [t1, ..., tn, t1^2, ..., tn^2] as polynomials
     * @throws AbortionException stops the action when the time has come
     */
    public Pair<ArrayList<VarPolynomial>, ArrayList<VarPolynomial>> toPolysWithSquares(final List<TRSTerm> terms,
        final FreshNameGenerator fng)
            throws AbortionException {
        this.aborter.checkAbortion();
        final ArrayList<VarPolynomial> resX = this.toPolys(terms, fng);
        final int termsSize = terms.size();
        final ArrayList<VarPolynomial> resY = new ArrayList<>(termsSize);
        // now iterate over these n polynomials, square them, and add them as well
        for (final VarPolynomial poly : resX) {
            final VarPolynomial polySquare = poly.power(2, this.aborter);
            resY.add(polySquare);
        }
        return new Pair<>(resX, resY);
    }

    /**
     * @param polysLeftRight - polynomials from the original lhs and rhs arguments
     * @param polysLeftRightSquares - polynomials from the squared lhs and rhs arguments
     * @param leftArity - the arity of the lhs
     * @param fng - fresh names
     * @return the massaged polynomials for the original lhs and rhs arguments AND
     *  the massaged polynomials for the squared lhs and rhs arguments AND
     *  the new massage variables that stand for squares
     */
    public Triple<ArrayList<VarPolynomial>, ArrayList<VarPolynomial>, Set<String>> abstractSquares(final ArrayList<VarPolynomial> polysLeftRight,
        final ArrayList<VarPolynomial> polysLeftRightSquares,
        final int leftArity,
        final FreshNameGenerator fng) {


        final int polysLeftRightSize = polysLeftRight.size();
        if (Globals.useAssertions) {
            assert polysLeftRightSize == polysLeftRightSquares.size() : polysLeftRightSize + " != "
                + polysLeftRightSquares.size() + '!';
        }

        final ArrayList<VarPolynomial> resX = new ArrayList<>(polysLeftRightSize);
        final ArrayList<VarPolynomial> resY = new ArrayList<>(polysLeftRightSize);

        final Set<String> squares = new LinkedHashSet<>();
        final Map<IndefinitePart, String> productToAbstractingVar = new LinkedHashMap<>();

        // the original lhss are ok by construction
        for (int i = 0; i < leftArity; ++i) {
            final VarPolynomial poly = polysLeftRight.get(i);
            if (Globals.useAssertions) {
                assert poly.isLinear();
            }
            resX.add(poly);
        }

        // the original rhss may have contained squares, abstract them
        for (int i = leftArity; i < polysLeftRightSize; ++i) {
            final VarPolynomial poly = polysLeftRight.get(i);
            final VarPolynomial massagedPoly = this.abstractSquaresInPoly(poly, productToAbstractingVar, squares, fng);
            resX.add(massagedPoly);
        }

        // the squared lhss and rhss most certainly contain squares, abstract them
        for (int i = 0; i < polysLeftRightSize; ++i) {
            final VarPolynomial poly = polysLeftRightSquares.get(i);
            final VarPolynomial massagedPoly = this.abstractSquaresInPoly(poly, productToAbstractingVar, squares, fng);
            resY.add(massagedPoly);
        }

        final Triple<ArrayList<VarPolynomial>, ArrayList<VarPolynomial>, Set<String>> res =
            new Triple<>(resX, resY, squares);
        return res;
    }

    /**
     * @param poly - we want to massage the squares out of it
     * @param productToAbstractingVar - tells for a product (currently: a square)
     *  what variable it has been massaged/abstracted to
     * @param squares - accumulator for variables that stand for squares;
     *  will be updated by the present method
     * @param fng - Fresh! Name! Generator! For replacement names.
     * @return a polynomial which is like poly, but massaged not to contain
     *  squares anymore
     */
    public VarPolynomial abstractSquaresInPoly(final VarPolynomial poly,
        final Map<IndefinitePart, String> productToAbstractingVar,
        final Set<String> squares,
        final FreshNameGenerator fng) {

        // if there is nothing to do, just return the original straight away
        if (poly.isLinear()) {
            return poly;
        }

        // ah, so there is some non-linearity! deal with it.
        final LinkedHashMap<IndefinitePart, SimplePolynomial> protoRes = new LinkedHashMap<>();
        for (final Entry<IndefinitePart, SimplePolynomial> monomial : poly.getVarMonomials().entrySet()) {
            final IndefinitePart iPart = monomial.getKey();
            final SimplePolynomial coeff = monomial.getValue();

            if (iPart.isLinear()) { // nothing to do for this one
                protoRes.put(iPart, coeff);
            } else { // look, it's non-linear!
                // sqrt( x^2*y^2*z ) = (x*y, z)
                final Pair<IndefinitePart, IndefinitePart> sqrtWithRest = iPart.sqrt();
                final IndefinitePart sqrt = sqrtWithRest.x;
                final IndefinitePart rest = sqrtWithRest.y;
                if (this.linearizeAll) { // we /will/ abstract the whole non-linear expression
                    // have we already seen our sqrt somewhere?
                    String replacement = productToAbstractingVar.get(iPart);
                    if (replacement == null) {
                        // ok, we want a new name for the square part
                        final String proposalName = Massager.proposeName(iPart);
                        replacement = fng.getFreshName(proposalName, false);
                        productToAbstractingVar.put(iPart, replacement);
                    }
                    final IndefinitePart massagedIPart = IndefinitePart.create(replacement, 1);
                    protoRes.put(massagedIPart, coeff);
                    if (rest.isEmpty()) {
                        squares.add(replacement);
                    }
                } else {
                    if (sqrt.isEmpty()) { // no squares found, so just keep the old IndefinitePart
                        protoRes.put(iPart, coeff);
                    } else {
                        // have we already seen our sqrt somewhere?
                        final IndefinitePart sqrtSquare = rest.isEmpty() ? iPart : sqrt.times(sqrt);
                        String replacement = productToAbstractingVar.get(sqrtSquare);
                        if (replacement == null) {
                            // ok, we want a new name for the square part
                            final String proposalName = Massager.proposeName(sqrtSquare);
                            replacement = fng.getFreshName(proposalName, false);
                            productToAbstractingVar.put(sqrtSquare, replacement);
                        }
                        final IndefinitePart massagedIPart = rest.times(IndefinitePart.create(replacement, 1));
                        protoRes.put(massagedIPart, coeff);
                    }
                }
            }
        }
        final VarPolynomial res = VarPolynomial.create(ImmutableCreator.create(protoRes));
        return res;
    }

    /**
     * Propose a name for a variable that abstracts iPart.
     *
     * @param iPart
     * @return a proposed name for a variable abstracting iPart
     */
    private static String proposeName(final IndefinitePart iPart) {
        return Massager.MASSAGE_VAR_PREFIX + '_' + iPart.toString().replace('^', 'P').replace('*', 'T') + '_';
    }

    /**
     * Propose a name for some variable.
     *
     * @return a proposed name for a variable
     */
    private String proposeName() {
        return Massager.MASSAGE_VAR_PREFIX_ABS + '_' + ++this.nameIndex;
    }

    /**
     * Add to conditions that square >= 0, square >= original, square >= -original.
     *
     * @param conditions - non-null, will be updated with knowledge on the square
     * @param square - stands for a square
     * @param original - stands for a term with original * original = square (null if term is not known)
     */
    private static void computeAbsConditions(final Collection<TRSTerm> conditions, final TRSTerm abs, final TRSTerm original) {
        // for now, the implementation of computeSquareConditions suspiciously does the same thing
        Massager.computeSquareConditions(conditions, abs, original);
    }

    /**
     * Add to conditions that square >= 0, square >= original, square >= -original.
     *
     * @param conditions - non-null, will be updated with knowledge on the square
     * @param square - stands for a square
     * @param original - stands for a term with original * original = square (null if term is not known)
     */
    private static void computeSquareConditions(final Collection<TRSTerm> conditions,
        final TRSTerm square,
        final TRSTerm original) {
        final TRSTerm geqZero = ToolBox.buildGe(square, ToolBox.buildInt(BigInteger.ZERO));
        conditions.add(geqZero);
        if (original != null) {
            final TRSTerm geqOriginal = ToolBox.buildGe(square, original);
            conditions.add(geqOriginal);
            final TRSTerm geqMinusOriginal = ToolBox.buildGe(square, ToolBox.buildMinus(original));
            conditions.add(geqMinusOriginal);
        }
        // TODO also add square == original * original?
        // May confuse the back-end, but tells the whole story.
        // -> check the caller "computeAbsConditions" before changing things here
    }

    /**
     * @return the massagedRulesToOriginalRules
     */
    public Map<IGeneralizedRule, IGeneralizedRule> getMassagedRulesToOriginalRules() {
        return this.massagedRulesToOriginalRules;
    }

    /**
     * @return the massagedSymsToOriginalSyms
     */
    public Map<FunctionSymbol, FunctionSymbol> getMassagedSymsToOriginalSyms() {
        return this.massagedSymsToOriginalSyms;
    }

    /**
     * @return the originalSymsToMassagedSyms
     */
    public Map<FunctionSymbol, FunctionSymbol> getOriginalSymsToMassagedSyms() {
        return this.originalSymsToMassagedSyms;
    }

    // * absolute: for abs_x we know abs_x >= 0 (bounded!) and abs_x >= x and abs_x >= -x and (x = abs_x or -x = abs_x).
    // * square: for xx we know xx >= 0 (bounded!) and xx >= x and xx >= -x.
    // * max: for max_x_y we know max_x_y >= x and max_x_y >= y and (max_x_y = x or max_x_y = y)
    // * absolute of product (= product of absolutes): for abs_xy we know that abs_xy >= 0 (bounded!) and (abs_xy = 0 or (abs_xy >= x and abs_xy >= y))
}
