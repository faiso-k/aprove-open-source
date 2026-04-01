package aprove.verification.dpframework.Orders.Solvers;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.POLO.Interpretation;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;
/**
 * Solves term constraints by searching for a suitable polynomial ordering.
 *
 * @author Andreas Capellmann, Carsten Fuhs
 * @version $Id$
 */
public class POLOSolver implements AbortableConstraintSolver<TRSTerm> {

    public String getProcessorName() {
        return "Generic POLO Solver";
    }

    private static Logger log =
        Logger.getLogger("aprove.verification.dpframework.Orders.Solvers.POLOSolver");

    /**
     * If this field is <code>true</code> the solver is free to return a weak monotonic polynomial
     * ordering as solution of the solve methods. Otherwise it searches for a strict monotonic
     * ordering.
     */
    private boolean allowWeakMonotonicity;

    /**
     * If we are dealing with context-sensitive rewriting and strict
     * monotonicity is required, in fact mu-monotonicity is sufficent.
     * Hence, if mu != null and ! allowWeakMonotonicity, we regard mu
     * to decide which argument positions of a given function symbol
     * must be treated with strong monotonicity.
     */
    private ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu;

    /**
     * In what way is the SPCSimplifier supposed to be invoked on the SPCs?
     */
    private final SimplificationMode simplificationMode;
    private final boolean simplifyAll;
    private final boolean stripExponents;


    private Interpretation interpretation;
    // the interpretation with which terms are to be interpreted by this

    private SearchAlgorithm searchAlgorithm;
    // search for a solution using searchAlgorithm

    /**
     * Creates a new POLOSolver which uses aborter, interpretation
     * and searchAlgorithm internally and which initially does
     * not allow weak monotonicity.
     *
     * @param aborter
     * @param interpretation the interpretation to be used
     * @param searchAlgorithm the search algorithm to be used
     */
    private POLOSolver(Interpretation interpretation,
            SearchAlgorithm searchAlgorithm,
            SimplificationMode simplificationMode,
            boolean simplifyAll, boolean stripExponents) {
        this.allowWeakMonotonicity = false;
        this.mu = null;
        this.interpretation = interpretation;
        this.searchAlgorithm = searchAlgorithm;
        this.simplificationMode = simplificationMode;
        this.simplifyAll = simplifyAll;
        this.stripExponents = stripExponents;
    }

    /**
     * Creates a new POLOSolver based on the polynomial interpretation
     * of function symbols interpretation. searchAlgorithm will be used
     * for finding solutions.
     *
     * @param interpretation - polynomial interpretation for function symbols
     * @param searchAlgorithm - search algorithm to be used for solution search
     * @param simplificationMode - in what way is the SPCSimplifier supposed to
     *  be used?
     * @param simplifyAll - true: simplify all constraints;
     *  false: also simplify searchstrict constraints
     * @param stripExponents - remove exponents for range 1?
     *  (p^n = p for 0 <= p <= 1)
     * @return the resulting POLOSolver (initially not allowing weak
     *  monotonicity)
     */
    public static POLOSolver create(Interpretation interpretation,
            SearchAlgorithm searchAlgorithm,
            SimplificationMode simplificationMode,
            boolean simplifyAll, boolean stripExponents) {
        return new POLOSolver(interpretation, searchAlgorithm,
                simplificationMode, simplifyAll, stripExponents);
    }


    /**
     * As per the contract of AbortableConstraintSolver, a collection of
     * term constraint is solved using the Abortion aborter, and the
     * solving order on terms is returned.
     *
     * @param cs the term constraints to be solved
     * @param aborter
     * @return the solving order on terms if found, null otherwise
     * @throws AbortionException
     */
    @Override
    public POLO solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) throws AbortionException {
        return this.solve (new LinkedHashSet<Constraint<TRSTerm>>(cs), aborter);
    }

    /**
     * Solves the constraints or delivers null if there was no success.
     *
     * @param aborter
     * @param constraints1 the polo-constraints to be solved, will be modified
     * @param constraints2 the polo-constraints to be solved
     * @return null, if no solution found; else the solving order
     */
    public POLO solve(Set<SimplePolyConstraint> constraints1, Abortion aborter, Set<VarPolyConstraint> constraints2) throws AbortionException {
        return this.solveWithoutOptimizing(aborter, constraints1, constraints2, null);
    }


    /**
     * Solves the constraints or delivers null if there was no success.
     *
     * @param aborter
     * @param constraints the polo-constraints to be solved
     * @return null, if no solution found; else the solving order
     */
    public POLO solve(Abortion aborter, Set<VarPolyConstraint> constraints) throws AbortionException {
        return this.solve(aborter, constraints, null);
    }

    /**
     * Solves the constraints or delivers null if there was no success.
     *
     * @param constraints1 The set of polo-constraints to be solved as such, may be null, will be modified
     * @param constraints2 The set of polo-constraints to be solved as such
     * @param searchStrictConstraints set of polo-constraints for
     *  the (term) constraints of type GE on which searchstrict is to be
     *  performed; null means not in searchstrict mode
     * @param aborter
     * @return null, if no solution found; the solving order, otherwise
     */
    public POLO solve(Set<SimplePolyConstraint> constraints1, Set<VarPolyConstraint> constraints2,
        Set<VarPolyConstraint> searchStrictConstraints,
        Abortion aborter) throws AbortionException {
        return this.solveWithoutOptimizing(aborter,
                constraints1, constraints2,
                searchStrictConstraints);
    }

    /**
     * Solves the constraints or delivers null if there was no success.
     * If maximizeMe != null and if the underlying SearchAlgorithm supports
     * this, an attempt to maximize the value will be made during the
     * search for a solution for the constraints.
     *
     * @param constraints1 The set of polo-constraints to be solved as such,
     *  may be null, will be modified
     * @param constraints2 The set of polo-constraints to be solved as such
     * @param searchStrictConstraints set of polo-constraints for
     *  the (term) constraints of type GE on which searchstrict is to be
     *  performed; null means not in searchstrict mode
     * @param maximizeMe If non-null, an attempt will be made to find a
     *  solution for the constraints such that maximizeMe is maximized
     * @param aborter
     * @return null, if no solution found; the solving order, otherwise
     */
    public POLO solve(Set<SimplePolyConstraint> constraints1, Set<VarPolyConstraint> constraints2,
        Set<VarPolyConstraint> searchStrictConstraints, SimplePolynomial maximizeMe,
        Abortion aborter) throws AbortionException {
        return this.actuallySolve(aborter,
                constraints1, constraints2,
                searchStrictConstraints, maximizeMe);
    }

    /**
     * Solves the constraints or delivers null if there was no success.
     *
     * @param aborter
     * @param constraints The set of polo-constraints to be solved
     *  as such
     * @param searchStrictConstraints set of polo-constraints for
     *  the (term) constraints of type GE on which searchstrict is to be
     *  performed; null means not in searchstrict mode
     * @return null, if no solution found; the solving order, otherwise
     */
    public POLO solve(Abortion aborter, Set<VarPolyConstraint> constraints,
        Set<VarPolyConstraint> searchStrictConstraints) throws AbortionException {
        return this.solveWithoutOptimizing(aborter, null,
                constraints,
                searchStrictConstraints);
    }

    /**
     * The suffix "withoutOptimizing" means that we don't make specific
     * attempts to orient as many of searchStrictConstraints as possible,
     * but are happy with at least a single one instead.
     *
     * @param aborter
     * @param constraints1
     * @param constraints2
     * @param searchStrictConstraints
     * @return
     * @throws AbortionException
     */
    private POLO solveWithoutOptimizing(Abortion aborter,
            Set<SimplePolyConstraint> constraints1, Set<VarPolyConstraint> constraints2,
            Set<VarPolyConstraint> searchStrictConstraints)
                                      throws AbortionException {
        return this.actuallySolve(aborter, constraints1, constraints2, searchStrictConstraints, null);
    }

    /**
     * Solves the constraints or delivers null if not successful.
     * If maximizeMe != null and if the underlying SearchAlgorithm supports
     * this, an attempt to maximize the value will be made during the
     * search for a solution for the constraints.
     *
     * @param constraints1 The set of polo-constraints to be solved as such, will be modified, may be null
     * @param constraints2 The set of polo-constraints to be solved as such
     * @param searchStrictConstraints set of polo-constraints for
     *  the (term) constraints of type GE on which searchstrict is
     *  to be performed; null means not in searchstrict mode
     * @param maximizeMe If non-null, an attempt will be made to find a
     *  solution for the constraints such that maximizeMe is maximized
     * @return null, if no solution found; the solving order, otherwise
     */
    private POLO actuallySolve(Abortion aborter,
            Set<SimplePolyConstraint> constraints1, Set<VarPolyConstraint> constraints2,
            Set<VarPolyConstraint> searchStrictConstraints, SimplePolynomial maximizeMe)
                                      throws AbortionException {

        /*
         * stage 1: Delete variables and add monotonicity constraints
         */
        Set<SimplePolyConstraint> simplePolyConstraints = constraints1 == null ? new LinkedHashSet<SimplePolyConstraint>() : constraints1;
        Set<SimplePolyConstraint> searchStrictSimplePolyConstraints;
        if (searchStrictConstraints == null) {
            searchStrictSimplePolyConstraints = new HashSet<SimplePolyConstraint>(0);
        } else {
            if (searchStrictConstraints.isEmpty()) {
                // one rule has to be oriented strictly, but there is none
                return null;
            }
            searchStrictSimplePolyConstraints = new LinkedHashSet<SimplePolyConstraint>(searchStrictConstraints.size());
            for (VarPolyConstraint varPolyConstraint : searchStrictConstraints) {
                Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> searchStrictSPCPair;
                searchStrictSPCPair = varPolyConstraint.createSearchStrictCoefficientConstraints();
                simplePolyConstraints.addAll(searchStrictSPCPair.x);
                searchStrictSimplePolyConstraints.add(searchStrictSPCPair.y);
            }
        }

        // from now on, searchStrictConstraints == emptyset means that
        // we are not in searchstrict mode, not that P is empty.

        for (VarPolyConstraint varPolyConstraint : constraints2) {
            simplePolyConstraints.addAll( varPolyConstraint.createCoefficientConstraints() );
        }

        if (! this.allowWeakMonotonicity) {
            POLOSolver.log.log(Level.CONFIG, "Creating monotonicity constraints\n");
            simplePolyConstraints.addAll(this.interpretation.getStrongMonotonicityConstraints(this.mu));
        }

        aborter.checkAbortion();

        /*
         * stage 2: simplify constraints and solve them
         */
        SimplifyingSearch simplSearch = SimplifyingSearch.create(this.searchAlgorithm,
                this.simplifyAll, this.stripExponents, this.simplificationMode);

        Map<String, BigInteger> goalState = simplSearch.search(simplePolyConstraints,
                searchStrictSimplePolyConstraints, maximizeMe, aborter);

        /*
         * stage 3: build order and store oriented rules
         */
        POLO solvingOrder;
        if (goalState != null) {
            final BigInteger defaultValue = BigInteger.ZERO;
            if (Globals.useAssertions) {
                // Has the SimplePolyConstraintSimplifier made any
                // inappropriate transformations?
                for (SimplePolyConstraint origSPC : simplePolyConstraints) {
                    assert origSPC.interpret(goalState, defaultValue);
                }
                for (SimplePolyConstraint origSPC : searchStrictSimplePolyConstraints) {
                    // at least check for non-strict orientation
                    assert origSPC.interpret(goalState, defaultValue);
                }
            }
            Interpretation interpretation = this.interpretation.specialize(goalState,
                    defaultValue);
            solvingOrder = POLO.create(interpretation);
            //storeOrientedSymbols();
        } else {
            solvingOrder = null;
        }
        return solvingOrder;
    }


    /**
     * Tries to solve a set of term constraints, possibly along with
     * searchstrict constraints.
     *
     * @param constraints the constraints to solve
     * @param searchStrictConstraints constraints of type GE, of which one
     *  will have to be ordered strictly; null indicates that we are not
     *  in searchstrict mode
     * @return the solving polynomial ordering
     *  (<code>null</code> if no solution could be found)
     * @throws AbortionException
     */
    public POLO solve(Set<Constraint<TRSTerm>> constraints,
            Set<Constraint<TRSTerm>> searchStrictConstraints, Abortion aborter) throws AbortionException {
        // generate compatibility constraints
        POLOSolver.log.log(Level.INFO, "Creating compatibility constraints\n");
        Set<VarPolyConstraint> cs = this.interpretation.getPolynomialConstraints(constraints, aborter);
        Set<VarPolyConstraint> searchStrictPolyCs;
        searchStrictPolyCs = (searchStrictConstraints == null) ? null : this.interpretation.getPolynomialConstraints(searchStrictConstraints, aborter);
        return this.solveWithoutOptimizing(aborter, null, cs, searchStrictPolyCs);
    }


    /**
     * Solves the constraints.
     *
     * @param aborter
     * @param constraints the constraints to solve
     * @return the solving polynomial ordering (<code>null</code> if no solution could be found)
     * @throws AbortionException
     */
    public POLO solve(Set<Constraint<TRSTerm>> constraints, Abortion aborter)
        throws AbortionException {
        return this.solve(constraints, null, aborter);
    }

    /**
     * @param fml
     * @param aborter
     * @return a POLO whose interpretation is a model of fml
     *  OR null if no such POLO is found
     * @throws AbortionException
     */
    public POLO solveDioFormula(Formula<Diophantine> fml, Abortion aborter) throws AbortionException {
        Map<String, BigInteger> goalState = this.searchAlgorithm.search(fml, aborter);
        POLO solvingOrder;
        if (goalState != null) {
            final BigInteger defaultValue = BigInteger.ZERO;
            Interpretation interpretation = this.interpretation.specialize(goalState,
                    defaultValue);
            solvingOrder = POLO.create(interpretation);
        } else {
            solvingOrder = null;
        }
        return solvingOrder;
    }


    /**
     * @param fml
     * @param specialSubformulae
     * @param aborter
     * @return a POLO whose interpretation is a model of fml and a model of
     *  as many <i>distinct</i> subformulae of specialSubformulae as possible
     *  OR null iff no such POLO is found
     * @throws AbortionException
     */
    public POLO solveMaxDioFormula(Formula<Diophantine> fml,
            Collection<Formula<Diophantine>> specialSubformulae,
            Abortion aborter) throws AbortionException {
        Map<String, BigInteger> goalState;
        if (this.searchAlgorithm instanceof MaxSearchAlgorithm) {
            MaxSearchAlgorithm maxSearchAlg = (MaxSearchAlgorithm) this.searchAlgorithm;
            goalState = maxSearchAlg.searchMax(fml, specialSubformulae, aborter);
        } else {
            POLOSolver.log.info(this.searchAlgorithm.getClass().getSimpleName() +
                    " does not support MaxSAT! Falling back to non-optimized search.\n");
            goalState = this.searchAlgorithm.search(fml, aborter);
        }
        POLO solvingOrder;
        if (goalState != null) {
            final BigInteger defaultValue = BigInteger.ZERO;
            Interpretation interpretation = this.interpretation.specialize(goalState,
                    defaultValue);
            solvingOrder = POLO.create(interpretation);
        } else {
            solvingOrder = null;
        }
        return solvingOrder;

    }


    public Interpretation getInterpretation() {
        return this.interpretation;
    }

    /**
     * Transforms (Term)constraints into (Polo)constraints
     * (i.e., VarPolyConstraints)
     */
    public Set<VarPolyConstraint> createPoloConstraints(Abortion aborter,
            Set<Constraint<TRSTerm>> constraints) throws AbortionException {
        return (this.interpretation.getPolynomialConstraints(constraints, aborter));
    }

    /**
     * Transforms (Term)constraints into SPCs (convenience method);
     * result may be modified.
     */
    public Set<SimplePolyConstraint> createPoloConstraints(Set<Constraint<TRSTerm>> constraints,
            Abortion aborter) throws AbortionException {
        Set<VarPolyConstraint> vpcs = this.createPoloConstraints(aborter, constraints);
        Set<SimplePolyConstraint> result = new LinkedHashSet<SimplePolyConstraint>();
        for (VarPolyConstraint vpc : vpcs) {
            vpc.addCoefficientConstraints(result);
        }
        return result;
    }

    /**
     * Creates POLO-Auto-Strict Constraint from Polo-Constraints of DPs
     */
    public void addASC(Set<VarPolyConstraint> dpConstraints) {
        this.interpretation.addAutoStrictConstraint(dpConstraints);
    }

    /**
     * Creates POLO-Auto-Strict Constraint from Polo-Constraints of DPs.
     * If new Diophantine vars are introduced (i.e., if jarAuto == false),
     * the range information of the encapsulated SearchAlgorithm is
     * modified to reflect this.
     *
     * @param dpConstraints - modified to contain autostrict constraint
     *  for the content before this method is called
     * @param jarAuto - use autostrict as described in JAR06?
     *   (true: one huge sum is used; false: new Dio vars are introduced)
     * @return polynomial p such that if you maximize p, you will orient
     *  the highest number of term constraints strictly
     */
    public SimplePolynomial addASC(Set<VarPolyConstraint> dpConstraints, boolean jarAuto) {
        Pair<SimplePolynomial, String[]> maxMeAndNewVars;
        maxMeAndNewVars = this.interpretation.addAutoStrictConstraint(dpConstraints, jarAuto);
        for (String a : maxMeAndNewVars.y) {
            this.searchAlgorithm.putRange(a, BigInteger.ONE);
        }
        return maxMeAndNewVars.x;
    }


    /**
     * @return whether this solver allows weak monotonicity
     * (i.e., whether coefficients of the interpreting polynomials may be zero,
     * which could lead to filtering variables)
     */
    public boolean getAllowWeakMonotonicity() {
        return this.allowWeakMonotonicity;
    }

    /**
     * @param allowWeakMonotonicity allowWeakMonotonicity?
     *  (i.e., may this solver use zero for coefficients, thus filtering
     *  some variables?)
     */
    public void setAllowWeakMonotonicity(boolean allowWeakMonotonicity) {
        this.allowWeakMonotonicity = allowWeakMonotonicity;
    }

    /**
     * @param mu the mu to set
     */
    public void setMu(ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        this.mu = mu;
    }
}
