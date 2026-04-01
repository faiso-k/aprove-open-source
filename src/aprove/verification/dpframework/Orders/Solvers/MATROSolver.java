package aprove.verification.dpframework.Orders.Solvers;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Solves a QDPProblem using Matrix Order.
 *
 * @author Patrick Kabasci
 * @version $Id: MATROSolver.java,v 1.10 2008/05/08 08:36:25 noschinski Exp $
 */
public class MATROSolver implements AbortableConstraintSolver<TRSTerm>{

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.Solvers.MATROSolver");


    private final boolean USE_DL = false;

    private final boolean rational;
    private final MatrixFactory fact;
    private final ArgumentInterpretor argInt;
    private TermInterpretor interpretor;
    private final SearchAlgorithm engine;
    private final int denominator;

    private BigInteger range;

    private final boolean newSearchStrict;


    private final boolean stripExponents;


    private final SimplificationMode simplificationMode;


    private final boolean simplifyAll;
    private boolean active;


    private boolean posFilter = false;

    private MATROSolver(final TermInterpretor interpretor,
            final MatrixFactory fact, final SearchAlgorithm engine,
            final ArgumentInterpretor argInt,
            final SimplificationMode simplificationMode,
            final boolean simplifyAll, final boolean stripExponents,
            final boolean dl, final boolean active,
            final boolean newSearchStrict, final boolean posFilter,
            final boolean rational, final int denominator) {
        this.interpretor = interpretor;
        this.fact = fact;
        this.engine = engine;
        this.argInt = argInt;
        this.simplificationMode = simplificationMode;
        this.simplifyAll = simplifyAll;
        this.stripExponents = stripExponents;
        this.rational = rational;
        //this.USE_DL = dl;
        this.active = active;
        this.newSearchStrict = newSearchStrict;
        this.posFilter = posFilter;
        this.denominator = denominator;
    }



    public static MATROSolver create(final TermInterpretor interpretor,
        final MatrixFactory fact,
        final SearchAlgorithm engine,
        final ArgumentInterpretor argInt,
        final SimplificationMode simplificationMode,
        final boolean simplifyAll,
        final boolean stripExponents,
        final boolean dl,
        final boolean active,
        final boolean newSearchStrict,
        final boolean posFilter,
        final boolean rational,
        final int denominator) {
        return new MATROSolver(interpretor, fact, engine, argInt,
            simplificationMode, simplifyAll, stripExponents, dl, active,
            newSearchStrict, posFilter, rational, denominator);
    }

    public static MATROSolver createPolComplexity(
            final SearchAlgorithm engine,
            final SimplificationMode simplificationMode,
            final boolean simplifyAll,
            final boolean stripExponents,
            final boolean active,
            final ImmutableSet<FunctionSymbol> dpsig,
            final ImmutableSet<FunctionSymbol> sig,
            final ImmutableSet<FunctionSymbol> monotonousSig,
            final ImmutableSet<FunctionSymbol> definedSig,
            final ImmutableSet<TRSVariable> vars,
            int dimension,
            BigInteger range
            ) {
        PolynomialComplexityTermInterpretor ti = new PolynomialComplexityTermInterpretor(dpsig, sig, vars, range, dimension, monotonousSig, definedSig);
        ArgumentInterpretor argInt = ti.getArgumentInterpretor();
        MatrixFactory fact = ti.getFactory();


        return new MATROSolver(ti, fact, engine, argInt,
                simplificationMode, simplifyAll, stripExponents, false, active,
                false, false, false, 1);
    }



    /*public static MATROSolver createRRR(TermInterpretor interpretor, int size, SearchAlgorithm engine, SimplificationMode simplificationMode, boolean simplifyAll, boolean stripExponents, boolean newSearchStrict) {
        return new MATROSolver(interpretor, new MonotonousMatrixFactory(size), engine, new LinearArgumentInterpretor(), simplificationMode, simplifyAll, stripExponents, false, false, newSearchStrict, false, false);
    }*/
    /**
     * This needs to be created. However, we usually try to find any strict rule, this method will just align everything GE
     * for whatever reason (none.)
     *
     */
    public ExportableOrder<TRSTerm> solve(final Map<Constraint<TRSTerm>, QActiveCondition> cs, final Abortion aborter) throws AbortionException {
        return this.solve(cs, null, aborter);
    }

    public Order<TRSTerm> solve(final Set<Rule> R, final Abortion aborter) throws AbortionException {

        // Creating constraints from rules...
        final Set<Constraint<TRSTerm>> constraints = Constraint.fromRules(R,OrderRelation.GE);

        return this.solve(constraints, aborter);



    }

    /**
     *  This custom method solves a RRR Matro problem, strictly by the Endrullis, Waldmann, Zantema method.
     *  To avoid correctness problems, it ignores all other parameters given, and reprograms itself.
     *  Thus, it is not possible to use the same MATROSolver instance both for a DP problem and a QTRS problem.
     *  TODO: This call will ensure a monotonic order is used, otherwise it will quit. (right now it simply overrides any strategy given and sets itself to monotonic.)
     *  @param cs   The constraints to be solved; if ALLSTRICT, all are aligned >
     */
    @Override
    public QActiveOrder solve(final Collection<Constraint<TRSTerm>> cs, final Abortion aborter) throws AbortionException {


        // To avoid null checks:
        if (cs == null) {
            return null; // sth went wrong;
        }

        // No need to care about active etc.


        // Hack due to RRR architecture
        final Set<FunctionSymbol> sig = new LinkedHashSet<FunctionSymbol> ();
        final Set<aprove.verification.dpframework.BasicStructures.TRSVariable> vars = new LinkedHashSet<aprove.verification.dpframework.BasicStructures.TRSVariable> ();
        sig.addAll(Constraint.getFunctionSymbols(cs));
        vars.addAll(Constraint.getVariables(cs));

        this.interpretor =
            new TermInterpretor(
                ImmutableCreator.create(new LinkedHashSet<FunctionSymbol>()),
                ImmutableCreator.create(sig), ImmutableCreator.create(vars),
                this.fact, this.argInt, this.range, this.rational,
                this.denominator);


        final Map<TRSTerm, Matrix> termInterpretations = new LinkedHashMap<TRSTerm, Matrix>();


        // signature collects all those function symbols in R and the non-root positions of P.
        // If a symbol both occurs in R and in the root symbols of P a flag is set (we cannot use certain factories)
        // and it is contained in signature nevertheless.
        final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();


        final long millis = System.currentTimeMillis();


        // Okay. These will be aligned.
        // These will be GE, but later on we will create searchStrict constraints
        final Collection<VarPolyConstraint> constraints = new ArrayList<VarPolyConstraint>();
        final Collection<VarPolyConstraint> anyStrictConstraints = new ArrayList<VarPolyConstraint>();
        for(final Constraint<TRSTerm> tc: cs) {


            tc.getLeft().collectFunctionSymbols(signature);
            tc.getRight().collectFunctionSymbols(signature);


            // Is this really GE or GR?
            if (Globals.useAssertions) {
                assert ((tc.getType() == OrderRelation.GE) | (tc.getType() == OrderRelation.GR)) ;
            }

            // Avoid calculating multiple times if the very same Term is used twice
            final TRSTerm leftTerm = tc.getLeft();
            Matrix interL = termInterpretations.get(leftTerm);
            if (interL == null) {
                interL = this.interpretor.interpretTerm(leftTerm);
                termInterpretations.put(leftTerm, interL);
            }
            final TRSTerm rightTerm = tc.getRight();
            Matrix interR = termInterpretations.get(rightTerm);
            if (interR == null) {
                interR = this.interpretor.interpretTerm(rightTerm);
                termInterpretations.put(rightTerm, interR);
            }
            if (tc.getType() == OrderRelation.GR) {
                // This one needs to be aligned, no searchstrict. May also be used to force autostrict.
                constraints.addAll(this.fact.getConstraints(interL, interR, ConstraintType.GT));
            } else {
                // This needs to be aligned GE. Furthermore we will peek the anystrict contstraint.
                constraints.addAll(this.fact.getConstraints(interL, interR, ConstraintType.GE));
                anyStrictConstraints.addAll(this.fact.getDPConstraints(interL, interR));
            }

            aborter.checkAbortion();

        }



        constraints.addAll(this.fact.getExtraConstraints(this.interpretor, signature));




        MATROSolver.log.log(Level.FINEST, "Interpretation took " + (System.currentTimeMillis()-millis) + "ms\n");
        // Now we need to convert all those VarPolyConstraints to
        // simplePoylConstraints which we can feed to a POLOsearcher.

        aborter.checkAbortion();
        final Set<SimplePolyConstraint> simpleConstraints = new LinkedHashSet<SimplePolyConstraint>();
        Set<SimplePolyConstraint> searchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();

        // This is straightforward for the constraints:
        for (final VarPolyConstraint c: constraints) {
            simpleConstraints.addAll (c.createCoefficientConstraints());
        }

        // But for the anyStrictConstraints, we also need to consider the Searchstrict constraint resulting.
        aborter.checkAbortion();
        for (final VarPolyConstraint c: anyStrictConstraints) {
            final Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> converted = c.createSearchStrictCoefficientConstraints();
            simpleConstraints.addAll(converted.x);
            searchStrictConstraints.add(converted.y);
        }


        final int constraintsNum = simpleConstraints.size() + searchStrictConstraints.size();


        Map<String, BigInteger> goalState;
        final Map<Integer, SimplePolynomial> alignConstraints = new LinkedHashMap<Integer, SimplePolynomial>();


        // No need for DL in RRR solver

        if (this.newSearchStrict || ((this.engine instanceof SatSearch) && ((SatSearch) this.engine).isMiniSAT2Incremental())) {
            int freshIndex=0;
            SimplePolynomial rsc = SimplePolynomial.create(0);
            for (final SimplePolyConstraint ssc: searchStrictConstraints) {
                final SimplePolynomial onePart = SimplePolynomial.create("tmp_MATROSolver_" + freshIndex++);
                alignConstraints .put(freshIndex - 1, onePart);
                simpleConstraints.add(new SimplePolyConstraint(ssc.getPolynomial().minus(onePart), ConstraintType.GE));
                rsc = rsc.plus(onePart);
            }
            searchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();
            simpleConstraints.add(new SimplePolyConstraint(rsc, ConstraintType.GT));
            MATROSolver.log.log(Level.FINEST, "Preparing for incremental search\n");
        }

        // Now we will simplify those constraints
        Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>> finalConstraintsWithMaps; // set of coefficient Constraints
        SimplePolyConstraintSimplifier spcSimplifier;
        long nanos1, nanosTotal;
        nanos1 = System.nanoTime();
        spcSimplifier = new SimplePolyConstraintSimplifier(simpleConstraints,
                searchStrictConstraints, this.engine.getRanges(), this.stripExponents);
        // TODO in case some Diophantine variables have a range other than
        // the default range, this should be represented in the above
        // DefaultValueMap, otherwise the above simplification might lead
        // to incompleteness

        finalConstraintsWithMaps =
            spcSimplifier.simplify(this.simplificationMode, this.simplifyAll,
                aborter);

        nanosTotal = System.nanoTime() - nanos1;
        if (MATROSolver.log.isLoggable(Level.FINEST)) {
            MATROSolver.log.log(Level.FINEST, "Polynomial constraint simplification took {0} ns.\n", nanosTotal);
        }
        if (finalConstraintsWithMaps == null) {
            if (MATROSolver.log.isLoggable(Level.FINEST)) {
                MATROSolver.log.log(Level.FINEST, "SimplePolyConstraintSimplifier has found the constraints to be UNSATISFIABLE for range {0}.\n",
                    this.engine.getRanges().getDefaultValue());
            }
            return null;
        }
        if (MATROSolver.log.isLoggable(Level.FINEST)) {
            MATROSolver.log.log(Level.FINEST, "SimplePolyConstraintSimplifier reduced problem by {0} constraints.\n",
                    constraintsNum - finalConstraintsWithMaps.x.size() - finalConstraintsWithMaps.w.size());
        }

        // Now we actually need to solve those constraints.
        aborter.checkAbortion();
        /*for (SimplePolyConstraint s: simpleConstraints) {
            log.log(Level.FINEST, s.toString() + "\n");
        }*/
        MATROSolver.log.log(Level.FINEST, "#Unknowns:" + this.fact.getCoeffConstraints().size() + "\n");
        if (this.engine instanceof SatSearch) {
            ((SatSearch)this.engine).getConverter().setNewRanges(this.interpretor.getRanges());
        }

        if (this.engine instanceof SatSearch && ((SatSearch) this.engine).isMiniSAT2Incremental()) {


            MATROSolver.log.log(Level.FINEST,"Entering incremental search.\n");
            SatSearch.IncrementalSearchInstance retInst;
            retInst = ((SatSearch) this.engine).multiSearch(finalConstraintsWithMaps.x, finalConstraintsWithMaps.w, ((SatSearch) this.engine).getConverter(), aborter);

            goalState = retInst.searchFirst();



            Map<String, BigInteger> newGoalState = goalState;

            while(newGoalState != null) {
                MATROSolver.log.log(Level.FINE, "An incremental instance found a solution.");
                goalState = newGoalState;
                final Iterator<Map.Entry<Integer, SimplePolynomial>> aliter = alignConstraints.entrySet().iterator();

                final Set<SimplePolyConstraint> newSpcs = new LinkedHashSet<SimplePolyConstraint>();
                while (aliter.hasNext()) {
                    final Map.Entry<Integer, SimplePolynomial> entry = aliter.next();
                    if (entry.getValue().specialize(goalState).equals(SimplePolynomial.ONE)) {
                        newSpcs.add(new SimplePolyConstraint(entry.getValue(), ConstraintType.GT));
                        aliter.remove();
                    }
                }
                newSpcs.add(new SimplePolyConstraint(SimplePolynomial.plus(alignConstraints.values()), ConstraintType.GT));

                newGoalState = retInst.searchNext(newSpcs, aborter);
            }


        } else {
            goalState = this.engine.search(finalConstraintsWithMaps.x, finalConstraintsWithMaps.w, aborter);
        }


        QActiveOrder solvingOrder;
        if (goalState != null) {
            final BigInteger defaultValue = BigInteger.ZERO;
            final SymbolRepresentations representation =  this.interpretor.getRepresentations().specialize(goalState, this.fact);

            if (Globals.useAssertions) {
                // Was POLO solving correct?

                for (final SimplePolyConstraint origSPC : simpleConstraints) {
                    assert origSPC.interpret(goalState, defaultValue);
                }
                for (final SimplePolyConstraint origSPC : searchStrictConstraints) {
                    // at least check for non-strict orientation
                    assert origSPC.interpret(goalState, defaultValue);
                }

                // Do we really fulfill MATRO constraints? Are we able to delete at least one rule? TODO: Allstrict
                final Map<TRSTerm, Matrix> specializedMatrices = new LinkedHashMap<TRSTerm, Matrix>();
                for (final Map.Entry<TRSTerm, Matrix> entry: termInterpretations.entrySet()) {
                    specializedMatrices.put(entry.getKey(), entry.getValue().specialize(goalState));
                }
                boolean foundStrict = cs.isEmpty();
                for (final Constraint<TRSTerm> constraint: cs) {
                    final Matrix leftmatrix = specializedMatrices.get(constraint.getLeft());
                    final Matrix rightmatrix = specializedMatrices.get(constraint.getRight());
                    if (!this.fact.hasSpecialOrder()) {
                        assert leftmatrix.isGE(rightmatrix);
                        foundStrict |= leftmatrix.isGT(rightmatrix);
                    } else {
                        assert this.fact.isGE(leftmatrix, rightmatrix);
                        foundStrict |= this.fact.isGT(leftmatrix, rightmatrix);
                    }
                }
                assert foundStrict;

            }


            solvingOrder = this.fact.getOrder(representation, this.interpretor, goalState, new LinkedHashMap<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>>(), new ActiveResolver());

        } else {
            solvingOrder = null;
        }

        return solvingOrder;



    }


    /**
     * Solves a matrix order problem, if a solution exists given the parameters preinstalled.
     * This is the solve version for the (highly restricted) polynomial runtime complexity derivations.
     * @param origcs    Map of term constraints to their active conditions; Will be aligned >= if active.
     * @param origdpcs  Set of DP constraints, of which at least one will be aligned >, the rest >=.
     * @param aborter   Aborter which will periodically be checked for timeouts.
     * @return          MATRO which fulfils the given criteria. Can then be used to extract the DP conditions strictly aligned.
     * @throws AbortionException
     */
    public QActiveOrder solveComplexity(final Map<Constraint<TRSTerm>, QActiveCondition> cs, Collection<Constraint<TRSTerm>> dpcs, final Abortion aborter) throws AbortionException {



        // Simply to avoid null-checks:
        if (dpcs == null) {
            dpcs = new TreeSet<Constraint<TRSTerm>>();
        }



        final Map<VarPolyConstraint, QActiveCondition> constraints = new LinkedHashMap<VarPolyConstraint, QActiveCondition>();
        final Set<VarPolyConstraint> dpconstraints = new LinkedHashSet<VarPolyConstraint>();

        final Map<TRSTerm, Matrix> termInterpretations = new LinkedHashMap<TRSTerm, Matrix>();


        // signature collects all those function symbols in R and the non-root positions of P.
        // If a symbol both occurs in R and in the root symbols of P a flag is set (we cannot use certain factories)
        // and it is contained in signature nevertheless.
        final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();


        final long millis = System.currentTimeMillis();





        final Map<FunctionSymbol, Set<Pair<Position, Constraint<TRSTerm>>>> cache = new LinkedHashMap<FunctionSymbol, Set<Pair<Position,Constraint<TRSTerm>>>>();
        new LinkedHashMap<FunctionSymbol, SimplePolynomial>();
        int runningNo = 0;


        // These will be GE, anything else is ignored.
        for(final Map.Entry<Constraint<TRSTerm>, QActiveCondition> tc: cs.entrySet()) {

            tc.getKey().getLeft().collectFunctionSymbols(signature);
            tc.getKey().getRight().collectFunctionSymbols(signature);

            // Is this really GE?
            if (Globals.useAssertions) {
                assert tc.getKey().getType() == OrderRelation.GE;
            }

            // Avoid calculating multiple times if the very same Term is used twice
            final TRSTerm leftTerm = tc.getKey().getLeft();
            Matrix interL = termInterpretations.get(leftTerm);
            final TRSTerm rightTerm = tc.getKey().getRight();
            Matrix interR = termInterpretations.get(rightTerm);

            if (interL == null) {
                if (this.rational) {
                    interL = this.interpretor.interpretTerm(leftTerm, 1, null, leftTerm, rightTerm.getDepth() > leftTerm.getDepth()? -(rightTerm.getDepth() - leftTerm.getDepth()):0);
                } else {
                    interL = this.interpretor.interpretTerm(leftTerm);
                    termInterpretations.put(leftTerm, interL);
                }
            }
            if (interR == null) {
                if (this.rational) {
                    interR = this.interpretor.interpretTerm(rightTerm, 1, null, rightTerm, leftTerm.getDepth() > rightTerm.getDepth()? -(leftTerm.getDepth() - rightTerm.getDepth()):0);
                } else {
                    interR = this.interpretor.interpretTerm(rightTerm);
                    termInterpretations.put(rightTerm, interR);
                }
            }
    //


            MATROSolver.log.log(Level.FINEST, leftTerm.toString() + "---- " + rightTerm.toString());
            MATROSolver.log.log(Level.FINEST, interL.toString() + " ---- " + interR.toString());
            constraints.putAll(this.toMap(this.fact.getConstraints(interL, interR, ConstraintType.GE), tc.getValue()));
            aborter.checkAbortion();

        }

        boolean includeLeftRoot = false;
        boolean includeRightRoot = false;


        // These will be aligned just in the same way, but later on we will create searchStrict constraints
        for(final Constraint<TRSTerm> tc: dpcs) {

            if (signature.contains(((TRSFunctionApplication)tc.getLeft()).getRootSymbol())) {
                // ROOT(P) and SIGNATURE(R) cup NON-ROOT-SIGNATURE(P) are not disjoint.
                if (!this.fact.supportsArbitraryQDP()) {

                }
                includeLeftRoot = true;
            }
            if (tc.getRight() instanceof TRSFunctionApplication) {
                if (signature.contains(((TRSFunctionApplication)tc.getRight()).getRootSymbol())) {
                    // ROOT(P) and SIGNATURE(R) cup NON-ROOT-SIGNATURE(P) are not disjoint.
                    if (!this.fact.supportsArbitraryQDP()) {

                    }
                    includeRightRoot = true;
                }
            }

            tc.getLeft().collectFunctionSymbols(signature);
            tc.getRight().collectFunctionSymbols(signature);
            if (tc.getRight() instanceof TRSFunctionApplication) {
                if (!includeRightRoot) {
                    signature.remove(((TRSFunctionApplication) tc.getRight()).getRootSymbol());

                }
            }
            if (!includeLeftRoot) {
                signature.remove(((TRSFunctionApplication) tc.getLeft()).getRootSymbol());
            }

            includeLeftRoot = false;
            includeRightRoot = false;

            // Is this really GE?
            if (Globals.useAssertions) {
                assert tc.getType() == OrderRelation.GE;
            }

            // Avoid calculating multiple times if the very same Term is used twice
            final TRSTerm leftTerm = tc.getLeft();
            Matrix interL = termInterpretations.get(leftTerm);
            final TRSTerm rightTerm = tc.getRight();
            Matrix interR = termInterpretations.get(rightTerm);

            if (interL == null) {
                if (this.rational) {
                    interL = this.interpretor.interpretTerm(leftTerm, 1, null, leftTerm, rightTerm.getDepth() > leftTerm.getDepth()? -(rightTerm.getDepth() - leftTerm.getDepth()):0);
                } else {
                    interL = this.interpretor.interpretTerm(leftTerm);
                    termInterpretations.put(leftTerm, interL);
                }
            }
            if (interR == null) {
                if (this.rational) {
                    interR = this.interpretor.interpretTerm(rightTerm, 1, null, rightTerm, leftTerm.getDepth() > rightTerm.getDepth()? -(leftTerm.getDepth() - rightTerm.getDepth()):0);
                } else {
                    interR = this.interpretor.interpretTerm(rightTerm);
                    termInterpretations.put(rightTerm, interR);
                }
            }

                MATROSolver.log.log(Level.FINEST, leftTerm.toString() + "---- " + rightTerm.toString());
                MATROSolver.log.log(Level.FINEST, interL.toString() + " ---- " + interR.toString());


            constraints.putAll(this.toMap(this.fact.getConstraints(interL, interR, ConstraintType.GE), QActiveCondition.TRUE));
            dpconstraints.addAll(this.fact.getDPConstraints(interL, interR));


            aborter.checkAbortion();

        }



        constraints.putAll(this.toMap(this.fact.getExtraConstraints(this.interpretor, signature), QActiveCondition.TRUE));




        MATROSolver.log.log(Level.FINEST, "Interpretation took " + (System.currentTimeMillis()-millis) + "ms\n");
        // Now we need to convert all those VarPolyConstraints to
        // simplePoylConstraints which we can feed to a POLOsearcher.

        aborter.checkAbortion();
        final Map<QActiveCondition, Set<SimplePolyConstraint>> simpleConstraints = new LinkedHashMap<QActiveCondition, Set<SimplePolyConstraint>>();
        Set<SimplePolyConstraint> searchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();

        // This is straightforward for the constraints:
        for (final Map.Entry<VarPolyConstraint, QActiveCondition> c: constraints.entrySet()) {
            this.merge(c.getKey().createCoefficientConstraints(), c.getValue(), simpleConstraints);
        }

        // But for the dpconstraints, we also need to consider the Searchstrict constraint resulting.
        aborter.checkAbortion();
        for (final VarPolyConstraint c: dpconstraints) {
            final Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> converted = c.createSearchStrictCoefficientConstraints();
            this.merge(converted.x, QActiveCondition.TRUE, simpleConstraints);
            searchStrictConstraints.add(converted.y);
        }


        final int constraintsNum = simpleConstraints.size() + searchStrictConstraints.size();


        Map<String, BigInteger> goalState;
        final Map<Integer, SimplePolynomial> alignConstraints = new LinkedHashMap<Integer, SimplePolynomial>();

        ActiveResolver activeResolver = new ActiveResolver();

        // Are we in DL or DC mode?
        if (this.engine.supportsDL() && this.USE_DL) {
            MATROSolver.log.log(Level.FINEST, "Using DL. \n");
            final FormulaFactory<Diophantine> ff = this.engine.getDLFactory();
            final List<Formula<Diophantine>> conjList = new ArrayList<Formula<Diophantine>>();
            final List<Formula<Diophantine>> disjList = new ArrayList<Formula<Diophantine>>();
            /*if (active) {
                conjList.add(DLActiveParser.convert(simpleConstraints, fact, argInt));

            } else {*/
                for (final Set<SimplePolyConstraint> cons: simpleConstraints.values()) {
                    for (final SimplePolyConstraint spc: cons) {
                        conjList.add(ff.buildTheoryAtom(Diophantine.create(spc)));
                    }
                }
            // Right now disable active in DL mode, there is no possibility to match assertions.
            /*}*/

            for (final SimplePolyConstraint cons: searchStrictConstraints) {
                conjList.add(ff.buildTheoryAtom(Diophantine.create(cons)));
                disjList.add(ff.buildTheoryAtom(Diophantine.create(cons.getPolynomial(), ConstraintType.GT)));
            }

            conjList.add(ff.buildOr(disjList));
            MATROSolver.log.log(Level.FINEST, "#Unknowns:" + this.fact.getCoeffConstraints().size() + "\n");
            if (this.engine instanceof SatSearch) {
                ((SatSearch)this.engine).getConverter().setNewRanges(this.interpretor.getRanges());
            }



            goalState = this.engine.search(ff.buildAnd(conjList), aborter);


        } else { // DC Mode
            Set<SimplePolyConstraint> flattenedConstraints = new LinkedHashSet<SimplePolyConstraint>();

            if (this.active) {
                final Pair<Set<SimplePolyConstraint>, ActiveResolver> p = DCActiveParser.convert(simpleConstraints, this.fact, this.argInt, aborter);
                flattenedConstraints = p.x;
                activeResolver = p.y;
            } else {
                for (final Set<SimplePolyConstraint> spcs: simpleConstraints.values()) {
                    flattenedConstraints.addAll(spcs);
                }
            }

            if (this.newSearchStrict || ((this.engine instanceof SatSearch) && ((SatSearch) this.engine).isMiniSAT2Incremental())) {
                int freshIndex=0;
                SimplePolynomial rsc = SimplePolynomial.create(0);
                for (final SimplePolyConstraint ssc: searchStrictConstraints) {
                    final SimplePolynomial onePart = SimplePolynomial.create("tmp_MATROSolver_" + freshIndex++);
                    alignConstraints .put(freshIndex - 1, onePart);
                    flattenedConstraints.add(new SimplePolyConstraint(ssc.getPolynomial().minus(onePart), ConstraintType.GE));
                    rsc = rsc.plus(onePart);
                }
                searchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();
                flattenedConstraints.add(new SimplePolyConstraint(rsc, ConstraintType.GT));
                MATROSolver.log.log(Level.FINEST, "Preparing for incremental search\n");
            }

            // Now we will simplify those constraints
            Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>> finalConstraintsWithMaps; // set of coefficient Constraints
            SimplePolyConstraintSimplifier spcSimplifier;
            long nanos1, nanosTotal;
            nanos1 = System.nanoTime();
            spcSimplifier = new SimplePolyConstraintSimplifier(flattenedConstraints,
                    searchStrictConstraints, this.engine.getRanges(), this.stripExponents);
            // TODO in case some Diophantine variables have a range other than
            // the default range, this should be represented in the above
            // DefaultValueMap, otherwise the above simplification might lead
            // to incompleteness

            finalConstraintsWithMaps =
                spcSimplifier.simplify(this.simplificationMode,
                    this.simplifyAll, aborter);

            nanosTotal = System.nanoTime() - nanos1;
            if (MATROSolver.log.isLoggable(Level.FINEST)) {
                MATROSolver.log.log(Level.FINEST, "Polynomial constraint simplification took {0} ns.\n", nanosTotal);
            }
            if (finalConstraintsWithMaps == null) {
                if (MATROSolver.log.isLoggable(Level.FINEST)) {
                    MATROSolver.log.log(Level.FINEST, "SimplePolyConstraintSimplifier has found the constraints to be UNSATISFIABLE for range {0}.\n",
                        this.engine.getRanges().getDefaultValue());
                }
                return null;
            }
            if (MATROSolver.log.isLoggable(Level.FINEST)) {
                MATROSolver.log.log(Level.FINEST, "SimplePolyConstraintSimplifier reduced problem by {0} constraints.\n",
                        constraintsNum - finalConstraintsWithMaps.x.size() - finalConstraintsWithMaps.w.size());
            }

            // Now we actually need to solve those contraints.
            aborter.checkAbortion();
            /*for (SimplePolyConstraint s: simpleConstraints) {
                log.log(Level.FINEST, s.toString() + "\n");
            }*/
            MATROSolver.log.log(Level.FINEST, "#Unknowns:" + this.fact.getCoeffConstraints().size() + "\n");
            if (this.engine instanceof SatSearch) {
                ((SatSearch)this.engine).getConverter().setNewRanges(this.interpretor.getRanges());
            }

            if (this.engine instanceof SatSearch && ((SatSearch) this.engine).isMiniSAT2Incremental()) {


                MATROSolver.log.log(Level.FINEST,"Entering incremental search.\n");
                SatSearch.IncrementalSearchInstance retInst;
                retInst = ((SatSearch) this.engine).multiSearch(finalConstraintsWithMaps.x, finalConstraintsWithMaps.w, ((SatSearch) this.engine).getConverter(), aborter);

                goalState = retInst.searchFirst();



                Map<String, BigInteger> newGoalState = goalState;

                while(newGoalState != null) {
                    MATROSolver.log.log(Level.FINE, "An incremental instance found a solution.");
                    goalState = newGoalState;
                    final Iterator<Map.Entry<Integer, SimplePolynomial>> aliter = alignConstraints.entrySet().iterator();

                    final Set<SimplePolyConstraint> newSpcs = new LinkedHashSet<SimplePolyConstraint>();
                    while (aliter.hasNext()) {
                        final Map.Entry<Integer, SimplePolynomial> entry = aliter.next();
                        if (entry.getValue().specialize(goalState).equals(SimplePolynomial.ONE)) {
                            newSpcs.add(new SimplePolyConstraint(entry.getValue(), ConstraintType.GT));
                            aliter.remove();
                        }
                    }
                    newSpcs.add(new SimplePolyConstraint(SimplePolynomial.plus(alignConstraints.values()), ConstraintType.GT));

                    newGoalState = retInst.searchNext(newSpcs, aborter);
                }


            } else {
                goalState = this.engine.search(finalConstraintsWithMaps.x, finalConstraintsWithMaps.w, aborter);
            }

        }

        //HACK!!! Some vital indefinites may be optimized away, this means they can be zero.
        if (goalState != null) {
            DefaultValueMap<String,BigInteger> dgoalState = new DefaultValueMap<String, BigInteger>(BigInteger.ZERO);
            dgoalState.putAll(goalState);
            goalState = dgoalState;
        }
        //END HACK

        activeResolver.specialize(goalState);
        QActiveOrder solvingOrder;
        if (goalState != null) {
            final SymbolRepresentations representation =  this.interpretor.getRepresentations().specialize(goalState, this.fact);


            if (Globals.useAssertions) {
                final TermInterpretor specti = new PolynomialComplexityTermInterpretor((PolynomialComplexityTermInterpretor)this.interpretor, goalState);


                /*for (Set<SimplePolyConstraint> origSPC : simpleConstraints.entrySet()) {
                    assert origSPC.interpret(goalState, defaultValue);
                }
                for (SimplePolyConstraint origSPC : searchStrictConstraints) {
                    // at least check for non-strict orientation
                    assert origSPC.interpret(goalState, defaultValue);
                }*/

                // Do we really fulfill MATRO constraints? Note that we have a special ordering on the constraints.
                final Map<TRSTerm, Matrix> specializedMatrices = new LinkedHashMap<TRSTerm, Matrix>();
                for (final Map.Entry<TRSTerm, Matrix> entry: termInterpretations.entrySet()) {
                    specializedMatrices.put(entry.getKey(), entry.getValue().specialize(goalState));
                }
                for (final Map.Entry<Constraint<TRSTerm>, QActiveCondition> entry : cs.entrySet()) {

                    if (activeResolver.get(entry.getValue())) {
                        assert specializedMatrices.get(entry.getKey().getLeft()).isGE(specializedMatrices.get(entry.getKey().getRight()));
                    }
                }
                boolean foundStrict = dpcs.isEmpty();
                for (final Constraint<TRSTerm> constraint: dpcs) {
                    final Matrix leftmatrix = specializedMatrices.get(constraint.getLeft());
                    final Matrix rightmatrix = specializedMatrices.get(constraint.getRight());
                    if (!this.fact.isGE(leftmatrix, rightmatrix)) {
                        // Something is terribly wrong.
                        MATROSolver.log.log(Level.WARNING, "Conflict found!================================");
                        MATROSolver.log.log(Level.WARNING, constraint.toString());
                        MATROSolver.log.log(Level.WARNING, "Left specialized Matrix:");
                        MATROSolver.log.log(Level.WARNING, leftmatrix.toString());
                        MATROSolver.log.log(Level.WARNING, "Right specialized Matrix:");
                        MATROSolver.log.log(Level.WARNING, rightmatrix.toString());
                        MATROSolver.log.log(Level.WARNING, "Original Matrices: Left:");
                        MATROSolver.log.log(Level.WARNING, termInterpretations.get(constraint.x).toString());
                        MATROSolver.log.log(Level.WARNING, "Original Matrices: Right:");
                        MATROSolver.log.log(Level.WARNING, termInterpretations.get(constraint.y).toString());
                        MATROSolver.log.log(Level.WARNING, "Failing here.");
                        assert false;
                    }
                    foundStrict |= this.fact.isGT(leftmatrix, rightmatrix);
                }
                assert foundStrict;

            }


            solvingOrder = PolComplexityMATRO.create(representation, this.interpretor, goalState, new LinkedHashMap<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>>(), activeResolver);


        } else {
            solvingOrder = null;
        }

        return solvingOrder;

    }





    /**
     * Solves a matrix order problem, if a solution exists given the parameters preinstalled.
     * @param origcs    Map of term constraints to their active conditions; Will be aligned >= if active.
     * @param origdpcs  Set of DP constraints, of which at least one will be aligned >, the rest >=.
     * @param aborter   Aborter which will periodically be checked for timeouts.
     * @return          MATRO which fulfils the given criteria. Can then be used to extract the DP conditions strictly aligned.
     * @throws AbortionException
     */
    public QActiveOrder solve(final Map<Constraint<TRSTerm>, QActiveCondition> origcs, Collection<Constraint<TRSTerm>> origdpcs, final Abortion aborter) throws AbortionException {




        // Simply to avoid null-checks:
        if (origdpcs == null) {
            origdpcs = new TreeSet<Constraint<TRSTerm>>();
        }



        final Map<VarPolyConstraint, QActiveCondition> constraints = new LinkedHashMap<VarPolyConstraint, QActiveCondition>();
        final Set<VarPolyConstraint> dpconstraints = new LinkedHashSet<VarPolyConstraint>();

        final Map<TRSTerm, Matrix> termInterpretations = new LinkedHashMap<TRSTerm, Matrix>();


        // signature collects all those function symbols in R and the non-root positions of P.
        // If a symbol both occurs in R and in the root symbols of P a flag is set (we cannot use certain factories)
        // and it is contained in signature nevertheless.
        final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();


        final long millis = System.currentTimeMillis();

        Collection<Constraint<TRSTerm>> dpcs;
        Map<Constraint<TRSTerm>, QActiveCondition> cs;
        Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>> hardCodedRelations;

        // This is for transformed Pairs. We need to denote which of these have been solved.

        final Triple<Map<Constraint<TRSTerm>, QActiveCondition>, Collection<Constraint<TRSTerm>>, Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>>> t = this.interpretor.transformQDP(origcs, origdpcs);
        dpcs = t.y;
        cs = t.x;
        hardCodedRelations = t.z;

        // We now use the transformed QDP to generate URwrtPF constraints, if enabled.

        // Note that we have to store the constraints on terms, it is not enough to store the terms.
        final Map<Constraint<TRSTerm>, Set<Pair<Position, Constraint<TRSTerm>>>> pfConstraints = new LinkedHashMap<Constraint<TRSTerm>, Set<Pair<Position,Constraint<TRSTerm>>>>();
        final Map<Constraint<TRSTerm>, SimplePolynomial> pfFormulae = new LinkedHashMap<Constraint<TRSTerm>, SimplePolynomial>();


        final Map<FunctionSymbol, Set<Pair<Position, Constraint<TRSTerm>>>> cache = new LinkedHashMap<FunctionSymbol, Set<Pair<Position,Constraint<TRSTerm>>>>();
        new LinkedHashMap<FunctionSymbol, SimplePolynomial>();
        int runningNo = 0;

        if (this.posFilter) {



            for (final Constraint<TRSTerm> c: dpcs) {
                // DP Constraints are always active, they only get the empty list.
                pfConstraints.put(c, new LinkedHashSet<Pair<Position,Constraint<TRSTerm>>>());
                pfFormulae.put(c, SimplePolynomial.ONE);
            }
            for (final Constraint<TRSTerm> c: cs.keySet()){
                // Constraints are said to be active if their root symbol is activated somewhere.
                pfFormulae.put(c, SimplePolynomial.create("PFC_" + runningNo++));
                final FunctionSymbol f = ((TRSFunctionApplication)(c.x)).getRootSymbol();
                if (cache.get(f) == null) {
                    // Gather the instances of this function symbol in terms.
                    cache.put(f, new LinkedHashSet<Pair<Position,Constraint<TRSTerm>>>());
                    for (final Constraint<TRSTerm> c2: dpcs) {
                       final Collection<Pair<Position, TRSTerm>> subTerms =  c2.y.getPositionsWithSubTerms();
                       for (final Pair<Position, TRSTerm> p: subTerms) {
                           if (p.y instanceof TRSFunctionApplication) {
                               if (((TRSFunctionApplication) p.y).getRootSymbol().equals(f)) {
                                   cache.get(f).add(new Pair<Position, Constraint<TRSTerm>>(p.x, c2));
                               }
                           }
                       }
                    }
                    for (final Constraint<TRSTerm> c2: cs.keySet()) {
                        final Collection<Pair<Position, TRSTerm>> subTerms =  c2.y.getPositionsWithSubTerms();
                        for (final Pair<Position, TRSTerm> p: subTerms) {
                            if (p.y instanceof TRSFunctionApplication) {
                                if (((TRSFunctionApplication) p.y).getRootSymbol().equals(f)) {
                                    cache.get(f).add(new Pair<Position, Constraint<TRSTerm>>(p.x, c2));
                                }
                            }
                        }
                     }

                }

                pfConstraints.put(c, cache.get(f));

            }

            // Before further compiling these, we need the interpretation.


            this.active = false; //PF and AF don't match.


        }
        final Set<SimplePolyConstraint> extraPFConstraints = new LinkedHashSet<SimplePolyConstraint>();

        // OK, here we can compile the extra PF constraints.
        if (this.posFilter) {

            for (final Constraint<TRSTerm> c: cs.keySet()) {

                SimplePolynomial finalPol = SimplePolynomial.ZERO;

                for (final Pair<Position, Constraint<TRSTerm>> p: pfConstraints.get(c)) {
                    SimplePolynomial result = pfFormulae.get(p.y);



                    final TRSFunctionApplication tm = (TRSFunctionApplication) p.y.y;

                    if (p.x.isEmptyPosition()) {
                      // Nothing to do, is active if rule is active.
                    } else {
                      FunctionSymbol fs = tm.getRootSymbol();
                      Matrix calc = null;
                      Matrix[] inter = new Matrix[fs.getArity()];
                      for (int i=0; i < fs.getArity(); i++) {
                          inter[i] = this.fact.Unity();
                      }
                      boolean firstTime = true; // Hack because we cannot use Unity here: Collapsing DPs
                      Position temp = Position.create();
                      for (final int i: p.x) {
                        fs = ((TRSFunctionApplication)tm.getSubterm(temp)).getRootSymbol();
                        inter = new Matrix[fs.getArity()];
                        for (int j=0; j < fs.getArity(); j++) {
                            inter[j] = this.fact.Unity();
                        }
                        if (firstTime) {
                            calc = Matrix.add(this.argInt.getFAppInterpretations(inter, fs, this.fact, i));
                            firstTime = false;


                            MatrixConstraint mc;
                            // Dirty hack for creating a null matrix of the appropriate size
                            mc= new MatrixConstraint(calc, calc.minus(calc), this.fact, ConstraintType.GE);
                            // We only care about the sum, and the left side. There is nothing negative here.
                            SimplePolynomial res = SimplePolynomial.ZERO;

                            for (final VarPolyConstraint vpc: mc.getVPCs()) {
                                // Simply take the left side, there are no variables, and add.
                                res = res.plus(vpc.getPolynomial().getConstantPart());
                            }

                        } else {
                          //calc.multiplyRight(Matrix.add(argInt.getFAppInterpretations(inter, fs, fact, i)));
                          calc = (Matrix.add(this.argInt.getFAppInterpretations(inter, fs, this.fact, i)));

                          MatrixConstraint mc;
                          // Dirty hack for creating a null matrix of the appropriate size
                          mc= new MatrixConstraint(calc, calc.minus(calc), this.fact, ConstraintType.GE);
                          // We only care about the sum, and the left side. There is nothing negative here.
                          SimplePolynomial res = SimplePolynomial.ZERO;

                          for (final VarPolyConstraint vpc: mc.getVPCs()) {
                              // Simply take the left side, there are no variables, and add.
                              res = res.plus(vpc.getPolynomial().getConstantPart());
                          }


                        }
                        temp = temp.append(i);
                      }
                      // Ok, this calc matrix is a chance to get it active, get its constraints and add them.

                      MatrixConstraint mc;
                      // Dirty hack for creating a null matrix of the appropriate size
                      mc= new MatrixConstraint(calc, calc.minus(calc), this.fact, ConstraintType.GE);
                      // We only care about the sum, and the left side. There is nothing negative here.
                      SimplePolynomial res = SimplePolynomial.ZERO;

                      for (final VarPolyConstraint vpc: mc.getVPCs()) {
                          // Simply take the left side, there are no variables, and add.
                          res = res.plus(vpc.getPolynomial().getConstantPart());
                      }
                      result = result.times(res);
                    }
                    finalPol = finalPol.plus(result);

                }

                extraPFConstraints.add(new SimplePolyConstraint(finalPol.minus(finalPol.times(pfFormulae.get(c))), ConstraintType.EQ));



            }
        }

        // Okay. These will be aligned.
        // These will be GE, anything else is ignored.
        for(final Map.Entry<Constraint<TRSTerm>, QActiveCondition> tc: cs.entrySet()) {

            tc.getKey().getLeft().collectFunctionSymbols(signature);
            tc.getKey().getRight().collectFunctionSymbols(signature);

            // Is this really GE?
            if (Globals.useAssertions) {
                assert tc.getKey().getType() == OrderRelation.GE;
            }

            // Avoid calculating multiple times if the very same Term is used twice
            final TRSTerm leftTerm = tc.getKey().getLeft();
            Matrix interL = termInterpretations.get(leftTerm);
            final TRSTerm rightTerm = tc.getKey().getRight();
            Matrix interR = termInterpretations.get(rightTerm);

            if (interL == null) {
                if (this.rational) {
                    interL = this.interpretor.interpretTerm(leftTerm, 1, null, leftTerm, rightTerm.getDepth() > leftTerm.getDepth()? -(rightTerm.getDepth() - leftTerm.getDepth()):0);
                } else {
                    interL = this.interpretor.interpretTerm(leftTerm);
                    termInterpretations.put(leftTerm, interL);
                }
            }
            if (interR == null) {
                if (this.rational) {
                    interR = this.interpretor.interpretTerm(rightTerm, 1, null, rightTerm, leftTerm.getDepth() > rightTerm.getDepth()? -(leftTerm.getDepth() - rightTerm.getDepth()):0);
                } else {
                    interR = this.interpretor.interpretTerm(rightTerm);
                    termInterpretations.put(rightTerm, interR);
                }
            }
    //


                MATROSolver.log.log(Level.FINEST, leftTerm.toString() + "---- " + rightTerm.toString());
                MATROSolver.log.log(Level.FINEST, interL.toString() + " ---- " + interR.toString());

            if (this.posFilter) {
                constraints.putAll(this.toMap(this.multiplyAll(pfFormulae.get(tc.getKey()) ,this.fact.getConstraints(interL, interR, ConstraintType.GE)), tc.getValue()));
            } else {
                constraints.putAll(this.toMap(this.fact.getConstraints(interL, interR, ConstraintType.GE), tc.getValue()));
            }
            aborter.checkAbortion();

        }

        boolean includeLeftRoot = false;
        boolean includeRightRoot = false;


        // These will be aligned just in the same way, but later on we will create searchStrict constraints
        for(final Constraint<TRSTerm> tc: dpcs) {

            if (signature.contains(((TRSFunctionApplication)tc.getLeft()).getRootSymbol())) {
                // ROOT(P) and SIGNATURE(R) cup NON-ROOT-SIGNATURE(P) are not disjoint.
                if (!this.fact.supportsArbitraryQDP()) {

                }
                includeLeftRoot = true;
            }
            if (tc.getRight() instanceof TRSFunctionApplication) {
                if (signature.contains(((TRSFunctionApplication)tc.getRight()).getRootSymbol())) {
                    // ROOT(P) and SIGNATURE(R) cup NON-ROOT-SIGNATURE(P) are not disjoint.
                    if (!this.fact.supportsArbitraryQDP()) {

                    }
                    includeRightRoot = true;
                }
            }

            tc.getLeft().collectFunctionSymbols(signature);
            tc.getRight().collectFunctionSymbols(signature);
            if (tc.getRight() instanceof TRSFunctionApplication) {
                if (!includeRightRoot) {
                    signature.remove(((TRSFunctionApplication) tc.getRight()).getRootSymbol());

                }
            }
            if (!includeLeftRoot) {
                signature.remove(((TRSFunctionApplication) tc.getLeft()).getRootSymbol());
            }

            includeLeftRoot = false;
            includeRightRoot = false;

            // Is this really GE?
            if (Globals.useAssertions) {
                assert tc.getType() == OrderRelation.GE;
            }

            // Avoid calculating multiple times if the very same Term is used twice
            final TRSTerm leftTerm = tc.getLeft();
            Matrix interL = termInterpretations.get(leftTerm);
            final TRSTerm rightTerm = tc.getRight();
            Matrix interR = termInterpretations.get(rightTerm);

            if (interL == null) {
                if (this.rational) {
                    interL = this.interpretor.interpretTerm(leftTerm, 1, null, leftTerm, rightTerm.getDepth() > leftTerm.getDepth()? -(rightTerm.getDepth() - leftTerm.getDepth()):0);
                } else {
                    interL = this.interpretor.interpretTerm(leftTerm);
                    termInterpretations.put(leftTerm, interL);
                }
            }
            if (interR == null) {
                if (this.rational) {
                    interR = this.interpretor.interpretTerm(rightTerm, 1, null, rightTerm, leftTerm.getDepth() > rightTerm.getDepth()? -(leftTerm.getDepth() - rightTerm.getDepth()):0);
                } else {
                    interR = this.interpretor.interpretTerm(rightTerm);
                    termInterpretations.put(rightTerm, interR);
                }
            }

                MATROSolver.log.log(Level.FINEST, leftTerm.toString() + "---- " + rightTerm.toString());
                MATROSolver.log.log(Level.FINEST, interL.toString() + " ---- " + interR.toString());


            dpconstraints.addAll(this.fact.getConstraints(interL, interR, ConstraintType.GE));
            aborter.checkAbortion();

        }



        constraints.putAll(this.toMap(this.fact.getExtraConstraints(this.interpretor, signature), QActiveCondition.TRUE));




        MATROSolver.log.log(Level.FINEST, "Interpretation took " + (System.currentTimeMillis()-millis) + "ms\n");
        // Now we need to convert all those VarPolyConstraints to
        // simplePoylConstraints which we can feed to a POLOsearcher.

        aborter.checkAbortion();
        final Map<QActiveCondition, Set<SimplePolyConstraint>> simpleConstraints = new LinkedHashMap<QActiveCondition, Set<SimplePolyConstraint>>();
        Set<SimplePolyConstraint> searchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();

        // This is straightforward for the constraints:
        for (final Map.Entry<VarPolyConstraint, QActiveCondition> c: constraints.entrySet()) {
            this.merge(c.getKey().createCoefficientConstraints(), c.getValue(), simpleConstraints);
        }

        // But for the dpconstraints, we also need to consider the Searchstrict constraint resulting.
        aborter.checkAbortion();
        for (final VarPolyConstraint c: dpconstraints) {
            final Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> converted = c.createSearchStrictCoefficientConstraints();
            this.merge(converted.x, QActiveCondition.TRUE, simpleConstraints);
            searchStrictConstraints.add(converted.y);
        }


        simpleConstraints.get(QActiveCondition.TRUE).addAll(extraPFConstraints);
        final int constraintsNum = simpleConstraints.size() + searchStrictConstraints.size();


        Map<String, BigInteger> goalState;
        final Map<Integer, SimplePolynomial> alignConstraints = new LinkedHashMap<Integer, SimplePolynomial>();

        ActiveResolver activeResolver = new ActiveResolver();

        // Are we in DL or DC mode?
        if (this.engine.supportsDL() && this.USE_DL) {
            MATROSolver.log.log(Level.FINEST, "Using DL. \n");
            final FormulaFactory<Diophantine> ff = this.engine.getDLFactory();
            final List<Formula<Diophantine>> conjList = new ArrayList<Formula<Diophantine>>();
            final List<Formula<Diophantine>> disjList = new ArrayList<Formula<Diophantine>>();
            /*if (active) {
                conjList.add(DLActiveParser.convert(simpleConstraints, fact, argInt));

            } else {*/
                for (final Set<SimplePolyConstraint> cons: simpleConstraints.values()) {
                    for (final SimplePolyConstraint spc: cons) {
                        conjList.add(ff.buildTheoryAtom(Diophantine.create(spc)));
                    }
                }
            // Right now disable active in DL mode, there is no possibility to match assertions.
            /*}*/

            for (final SimplePolyConstraint cons: searchStrictConstraints) {
                conjList.add(ff.buildTheoryAtom(Diophantine.create(cons)));
                disjList.add(ff.buildTheoryAtom(Diophantine.create(cons.getPolynomial(), ConstraintType.GT)));
            }

            conjList.add(ff.buildOr(disjList));
            MATROSolver.log.log(Level.FINEST, "#Unknowns:" + this.fact.getCoeffConstraints().size() + "\n");
            if (this.engine instanceof SatSearch) {
                ((SatSearch)this.engine).getConverter().setNewRanges(this.interpretor.getRanges());
            }

            try {
            final File f = new File("/home/kabasci/testout.dio");

            final FileWriter s = new FileWriter(f);
            s.write(ff.buildAnd(conjList).toString());
            s.flush();

            } catch (final Exception ex) {
            }




            goalState = this.engine.search(ff.buildAnd(conjList), aborter);


        } else { // DC Mode
            Set<SimplePolyConstraint> flattenedConstraints = new LinkedHashSet<SimplePolyConstraint>();

            if (this.active) {
                final Pair<Set<SimplePolyConstraint>, ActiveResolver> p = DCActiveParser.convert(simpleConstraints, this.fact, this.argInt, aborter);
                flattenedConstraints = p.x;
                activeResolver = p.y;
            } else {
                for (final Set<SimplePolyConstraint> spcs: simpleConstraints.values()) {
                    flattenedConstraints.addAll(spcs);
                }
            }

            if (this.newSearchStrict || ((this.engine instanceof SatSearch) && ((SatSearch) this.engine).isMiniSAT2Incremental())) {
                int freshIndex=0;
                SimplePolynomial rsc = SimplePolynomial.create(0);
                for (final SimplePolyConstraint ssc: searchStrictConstraints) {
                    final SimplePolynomial onePart = SimplePolynomial.create("tmp_MATROSolver_" + freshIndex++);
                    alignConstraints .put(freshIndex - 1, onePart);
                    flattenedConstraints.add(new SimplePolyConstraint(ssc.getPolynomial().minus(onePart), ConstraintType.GE));
                    rsc = rsc.plus(onePart);
                }
                searchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();
                flattenedConstraints.add(new SimplePolyConstraint(rsc, ConstraintType.GT));
                MATROSolver.log.log(Level.FINEST, "Preparing for incremental search\n");
            }

            // Now we will simplify those constraints
            Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>> finalConstraintsWithMaps; // set of coefficient Constraints
            SimplePolyConstraintSimplifier spcSimplifier;
            long nanos1, nanosTotal;
            nanos1 = System.nanoTime();
            spcSimplifier = new SimplePolyConstraintSimplifier(flattenedConstraints,
                    searchStrictConstraints, this.engine.getRanges(), this.stripExponents);
            // TODO in case some Diophantine variables have a range other than
            // the default range, this should be represented in the above
            // DefaultValueMap, otherwise the above simplification might lead
            // to incompleteness

            finalConstraintsWithMaps =
                spcSimplifier.simplify(this.simplificationMode,
                    this.simplifyAll, aborter);

            nanosTotal = System.nanoTime() - nanos1;
            if (MATROSolver.log.isLoggable(Level.FINEST)) {
                MATROSolver.log.log(Level.FINEST, "Polynomial constraint simplification took {0} ns.\n", nanosTotal);
            }
            if (finalConstraintsWithMaps == null) {
                if (MATROSolver.log.isLoggable(Level.FINEST)) {
                    MATROSolver.log.log(Level.FINEST, "SimplePolyConstraintSimplifier has found the constraints to be UNSATISFIABLE for range {0}.\n",
                        this.engine.getRanges().getDefaultValue());
                }
                return null;
            }
            if (MATROSolver.log.isLoggable(Level.FINEST)) {
                MATROSolver.log.log(Level.FINEST, "SimplePolyConstraintSimplifier reduced problem by {0} constraints.\n",
                        constraintsNum - finalConstraintsWithMaps.x.size() - finalConstraintsWithMaps.w.size());
            }

            // Now we actually need to solve those contraints.
            aborter.checkAbortion();
            /*for (SimplePolyConstraint s: simpleConstraints) {
                log.log(Level.FINEST, s.toString() + "\n");
            }*/
            MATROSolver.log.log(Level.FINEST, "#Unknowns:" + this.fact.getCoeffConstraints().size() + "\n");
            if (this.engine instanceof SatSearch) {
                ((SatSearch)this.engine).getConverter().setNewRanges(this.interpretor.getRanges());
            }

            if (this.engine instanceof SatSearch && ((SatSearch) this.engine).isMiniSAT2Incremental()) {


                MATROSolver.log.log(Level.FINEST,"Entering incremental search.\n");
                SatSearch.IncrementalSearchInstance retInst;
                retInst = ((SatSearch) this.engine).multiSearch(finalConstraintsWithMaps.x, finalConstraintsWithMaps.w, ((SatSearch) this.engine).getConverter(), aborter);

                goalState = retInst.searchFirst();



                Map<String, BigInteger> newGoalState = goalState;

                while(newGoalState != null) {
                    MATROSolver.log.log(Level.FINE, "An incremental instance found a solution.");
                    goalState = newGoalState;
                    final Iterator<Map.Entry<Integer, SimplePolynomial>> aliter = alignConstraints.entrySet().iterator();

                    final Set<SimplePolyConstraint> newSpcs = new LinkedHashSet<SimplePolyConstraint>();
                    while (aliter.hasNext()) {
                        final Map.Entry<Integer, SimplePolynomial> entry = aliter.next();
                        if (entry.getValue().specialize(goalState).equals(SimplePolynomial.ONE)) {
                            newSpcs.add(new SimplePolyConstraint(entry.getValue(), ConstraintType.GT));
                            aliter.remove();
                        }
                    }
                    newSpcs.add(new SimplePolyConstraint(SimplePolynomial.plus(alignConstraints.values()), ConstraintType.GT));

                    newGoalState = retInst.searchNext(newSpcs, aborter);
                }


            } else {
                goalState = this.engine.search(finalConstraintsWithMaps.x, finalConstraintsWithMaps.w, aborter);
            }

        }

        activeResolver.specialize(goalState);
        QActiveOrder solvingOrder;
        if (goalState != null) {
            final SymbolRepresentations representation =  this.interpretor.getRepresentations().specialize(goalState, this.fact);


            if (Globals.useAssertions) {
                final TermInterpretor specti = new TermInterpretor(this.interpretor, goalState);


                /*for (Set<SimplePolyConstraint> origSPC : simpleConstraints.entrySet()) {
                    assert origSPC.interpret(goalState, defaultValue);
                }
                for (SimplePolyConstraint origSPC : searchStrictConstraints) {
                    // at least check for non-strict orientation
                    assert origSPC.interpret(goalState, defaultValue);
                }*/

                // Do we really fulfill MATRO constraints? Or do we have a special ordering?
                final Map<TRSTerm, Matrix> specializedMatrices = new LinkedHashMap<TRSTerm, Matrix>();
                for (final Map.Entry<TRSTerm, Matrix> entry: termInterpretations.entrySet()) {
                    specializedMatrices.put(entry.getKey(), entry.getValue().specialize(goalState));
                }
                for (final Map.Entry<Constraint<TRSTerm>, QActiveCondition> entry : cs.entrySet()) {

                    if (activeResolver.get(entry.getValue())) {
                        if (!this.fact.hasSpecialOrder() && !this.rational) {
                            assert specializedMatrices.get(entry.getKey().getLeft()).isGE(specializedMatrices.get(entry.getKey().getRight()));
                        } else if (this.rational) {
                            // For rational we always have to reinterpret, since depth of the other term is an issue.
                            final TRSTerm leftTerm = entry.getKey().getLeft();
                            final TRSTerm rightTerm = entry.getKey().getRight();
                            final Matrix l =  specti.interpretTerm(leftTerm, 1, null, leftTerm, rightTerm.getDepth() > leftTerm.getDepth()? -(rightTerm.getDepth() - leftTerm.getDepth()):0);
                            final Matrix r =  specti.interpretTerm(rightTerm, 1, null, rightTerm, leftTerm.getDepth() > rightTerm.getDepth()? -(leftTerm.getDepth() - rightTerm.getDepth()):0);
                            assert this.fact.isGE(l, r);
                        } else {
                            assert this.fact.isGE(specializedMatrices.get(entry.getKey().getLeft()), (specializedMatrices.get(entry.getKey().getRight())));
                        }
                    }
                }
                boolean foundStrict = dpcs.isEmpty();
                for (final Constraint<TRSTerm> constraint: dpcs) {
                    final Matrix leftmatrix = specializedMatrices.get(constraint.getLeft());
                    final Matrix rightmatrix = specializedMatrices.get(constraint.getRight());
                    if (!this.fact.hasSpecialOrder() && !this.rational) {
                        assert leftmatrix.isGE(rightmatrix);
                        foundStrict |= leftmatrix.isGT(rightmatrix);
                    } else if (this.rational) {
                        // For rational we always have to reinterpret, since depth of the other term is an issue.
                        final TRSTerm leftTerm = constraint.getLeft();
                        final TRSTerm rightTerm = constraint.getRight();
                        final Matrix l =
                            specti.interpretTerm(
                                leftTerm,
                                1,
                                null,
                                leftTerm,
                                rightTerm.getDepth() > leftTerm.getDepth()
                                    ? -(rightTerm.getDepth() - leftTerm.getDepth())
                                    : 0);
                        final Matrix r =
                            specti.interpretTerm(
                                rightTerm,
                                1,
                                null,
                                rightTerm,
                                leftTerm.getDepth() > rightTerm.getDepth()
                                    ? -(leftTerm.getDepth() - rightTerm.getDepth())
                                    : 0);
                        assert this.fact.isGE(l, r);
                        foundStrict |= this.fact.isGT(l, r);

                    } else {
                        assert this.fact.isGE(leftmatrix, rightmatrix);
                        foundStrict |= this.fact.isGT(leftmatrix, rightmatrix);
                    }
                }
                assert foundStrict;

            }


            if (!this.fact.hasSpecialOrder()) {
                solvingOrder = MATRO.create(representation, this.interpretor, goalState, hardCodedRelations, activeResolver);
            } else {
                solvingOrder = this.fact.getOrder(representation, this.interpretor, goalState, hardCodedRelations, activeResolver);
            }

        } else {
            solvingOrder = null;
        }

        return solvingOrder;

    }


    /**
     * Solves a diophine Formula
     * 
     * @param fml
     * @param aborter
     * @return a MATRO whose interpretation is a model of fml
     *  OR null if no such MATRO is found
     * @throws AbortionException
     */
    public MATRO solveDioFormula(Formula<Diophantine> fml, Abortion aborter) throws AbortionException {
        Map<String, BigInteger> goalState = this.engine.search(fml, aborter);
        MATRO solvingOrder;
        if (goalState != null) {
            final SymbolRepresentations representation =  this.interpretor.getRepresentations().specialize(goalState, this.fact);
            solvingOrder = MATRO.create(representation, this.interpretor, goalState, new LinkedHashMap<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>>(), new ActiveResolver());
        } else {
            solvingOrder = null;
        }
        return solvingOrder;
    }
    
    public TermInterpretor getInterpretation() {
        return this.interpretor;
    }
    
    public MatrixFactory getFact() {
        return this.fact;
    }
    
    private Collection<VarPolyConstraint> multiplyAll(final SimplePolynomial polynomial, final Collection< ? extends VarPolyConstraint> constraints) {
        final LinkedHashSet<VarPolyConstraint> result = new LinkedHashSet<VarPolyConstraint>();

        for (final VarPolyConstraint vpc: constraints) {
            result.add (new VarPolyConstraint (vpc.getPolynomial().times(polynomial), vpc.getType()));
        }

        return result;
    }





    private void merge(final Set<SimplePolyConstraint> spcs, final QActiveCondition cond, final Map<QActiveCondition, Set<SimplePolyConstraint>> constraints) {
        if (constraints.containsKey(cond)) {
            constraints.get(cond).addAll(spcs);
        } else {
            constraints.put(cond, spcs);
        }
    }



    private <T> Map<T, QActiveCondition> toMap(final Collection<T> constraints, final QActiveCondition value) {
        final Map<T, QActiveCondition> retMap = new LinkedHashMap<T, QActiveCondition>();
        for (final T vpc: constraints) {
            retMap.put(vpc, value);
        }
        return retMap;
    }


    @Deprecated
    public static MATROSolver createRRR(final MatrixFactory fact2, final SearchAlgorithm searchAlg, final ArgumentInterpretor ai, final SimplificationMode simplificationMode2, final boolean simplifyAll2, final boolean stripExponents2, final Boolean dl, final Boolean newsearchstrict, final Boolean pf, final int range) {

        // deprecated
        /*final MATROSolver solver = new MATROSolver(null, fact2, searchAlg, ai, simplificationMode2, simplifyAll2, stripExponents2, dl, false, newsearchstrict, pf, false);
        solver.range = range;
        return solver;
        */
        return null;

    }






}

