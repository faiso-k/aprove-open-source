package aprove.verification.dpframework.Orders.Solvers;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.LimitPolynomials.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Solves a QDPProblem using Matrix Order.
 *
 * @author Patrick Kabasci
 * @version $Id: MATROSolver.java,v 1.10 2008/05/08 08:36:25 noschinski Exp $
 */
public class LimitPOLOSolver implements AbortableConstraintSolver<TRSTerm>{

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.Solvers.LimitPOLOSolver");


    private LPOLInterpretor inter;
    private final SearchAlgorithm engine;

    private BigInteger range;

    private final boolean newSearchStrict;


    private final boolean stripExponents;


    private final SimplificationMode simplificationMode;


    private final boolean simplifyAll;

    // TODO: Forced false by now!
    private boolean active = false;



    private LimitPOLOSolver(final LPOLInterpretor interpretor,
            final SearchAlgorithm engine,
            final SimplificationMode simplificationMode,
            final boolean simplifyAll, final boolean stripExponents,
            final boolean active,
            final boolean newSearchStrict) {
        this.inter = interpretor;
        this.engine = engine;
        this.simplificationMode = simplificationMode;
        this.simplifyAll = simplifyAll;
        this.stripExponents = stripExponents;
        //TODO this.active = active;
        this.newSearchStrict = newSearchStrict;
    }



    public static LimitPOLOSolver create(final LPOLInterpretor interpretor,
        final SearchAlgorithm engine,
        final SimplificationMode simplificationMode,
        final boolean simplifyAll, final boolean stripExponents,
        final boolean active,
        final boolean newSearchStrict) {
        return new LimitPOLOSolver(interpretor, engine,
            simplificationMode, simplifyAll, stripExponents, active,
            newSearchStrict);
    }

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
     * Solves a limitational polynomial order problem, if a solution exists given the parameters passed.
     * @param origcs    Map of term constraints to their active conditions; Will be aligned >= if active.
     * @param origdpcs  Set of DP constraints, of which at least one will be aligned >, the rest >=.
     * @param aborter   Aborter which will periodically be checked for timeouts.
     * @return          LimitPOLO which fulfils the given criteria. Can then be used to extract the DP conditions strictly aligned.
     * @throws AbortionException
     */
    public QActiveOrder solve(final Map<Constraint<TRSTerm>, QActiveCondition> cs, Collection<Constraint<TRSTerm>> dpcs, final Abortion aborter) throws AbortionException {

        // Simply to avoid null-checks:
        if (dpcs == null) {
            dpcs = new TreeSet<Constraint<TRSTerm>>();
        }



        final Map<SimplePolyConstraint, QActiveCondition> constraints = new LinkedHashMap<SimplePolyConstraint, QActiveCondition>();
        final Set<SimplePolyConstraint> dpconstraints = new LinkedHashSet<SimplePolyConstraint>();

        final Map<TRSTerm, LimitVarPolynomial> termInterpretations = new LinkedHashMap<TRSTerm, LimitVarPolynomial>();


        // signature collects all those function symbols in R and the non-root positions of P.
        // If a symbol both occurs in R and in the root symbols of P a flag is set (we cannot use certain factories)
        // and it is contained in signature nevertheless.
        final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();


        final long millis = System.currentTimeMillis();


        // This is for transformed Pairs. We need to denote which of these have been solved.





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

            LimitVarPolynomialConstraint res = this.inter.interpretRule(tc.getKey());

            Pair<List<SimplePolyConstraint>, SimplePolyConstraint> resP = LVPCToVPCEncoder.encodeSearchStrict(res);

            constraints.putAll(this.toMap( resP.x , tc.getValue()));

            aborter.checkAbortion();

        }

        boolean includeLeftRoot = false;
        boolean includeRightRoot = false;


        // These will be aligned just in the same way, but later on we will create searchStrict constraints
        for(final Constraint<TRSTerm> tc: dpcs) {

            tc.getLeft().collectFunctionSymbols(signature);
            tc.getRight().collectFunctionSymbols(signature);


            // Is this really GE?
            if (Globals.useAssertions) {
                assert tc.getType() == OrderRelation.GE;
            }
            LimitVarPolynomialConstraint res = this.inter.interpretRule(tc);

            Pair<List<SimplePolyConstraint>, SimplePolyConstraint> resP = LVPCToVPCEncoder.encodeSearchStrict(res);

            constraints.putAll(this.toMap( resP.x , QActiveCondition.TRUE));

            dpconstraints.add(resP.y);
            aborter.checkAbortion();

        }

        // Ensure all exponents are in the allowed range.
        constraints.putAll(this.toMap(this.inter.getRepresentations().getExpRangeConstraints(), QActiveCondition.TRUE));



        LimitPOLOSolver.log.log(Level.FINEST, "Interpretation took " + (System.currentTimeMillis()-millis) + "ms\n");
        // Now we need to convert all those VarPolyConstraints to
        // simplePoylConstraints which we can feed to a POLOsearcher.

        aborter.checkAbortion();
        final Map<QActiveCondition, Set<SimplePolyConstraint>> simpleConstraints = new LinkedHashMap<QActiveCondition, Set<SimplePolyConstraint>>();
        Set<SimplePolyConstraint> searchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();

        // This is straightforward for the constraints:
        for (final Map.Entry<SimplePolyConstraint, QActiveCondition> c: constraints.entrySet()) {
            this.merge(Collections.singleton(c.getKey()), c.getValue(), simpleConstraints);
        }

        // But for the dpconstraints, we also need to consider the Searchstrict constraint resulting.
        aborter.checkAbortion();
        for (final SimplePolyConstraint c: dpconstraints) {
            searchStrictConstraints.add(c);
        }


        final int constraintsNum = simpleConstraints.size() + searchStrictConstraints.size();


        Map<String, BigInteger> goalState;
        final Map<Integer, SimplePolynomial> alignConstraints = new LinkedHashMap<Integer, SimplePolynomial>();

        ActiveResolver activeResolver = new ActiveResolver();


        Set<SimplePolyConstraint> flattenedConstraints = new LinkedHashSet<SimplePolyConstraint>();

        if (this.active) {
            // TODO: Active!
            for (final Set<SimplePolyConstraint> spcs: simpleConstraints.values()) {
                flattenedConstraints.addAll(spcs);
            }
        } else {
            for (final Set<SimplePolyConstraint> spcs: simpleConstraints.values()) {
                flattenedConstraints.addAll(spcs);
            }
        }

        if (this.newSearchStrict || ((this.engine instanceof SatSearch) && ((SatSearch) this.engine).isMiniSAT2Incremental())) {
            int freshIndex=0;
            SimplePolynomial rsc = SimplePolynomial.create(0);
            for (final SimplePolyConstraint ssc: searchStrictConstraints) {
                final SimplePolynomial onePart = SimplePolynomial.create("tmp_LimPoloSolver_" + freshIndex++);
                alignConstraints .put(freshIndex - 1, onePart);
                flattenedConstraints.add(new SimplePolyConstraint(ssc.getPolynomial().minus(onePart), ConstraintType.GE));
                rsc = rsc.plus(onePart);
            }
            searchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();
            flattenedConstraints.add(new SimplePolyConstraint(rsc, ConstraintType.GT));
            LimitPOLOSolver.log.log(Level.FINEST, "Preparing for incremental search\n");
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
        if (LimitPOLOSolver.log.isLoggable(Level.FINEST)) {
            LimitPOLOSolver.log.log(Level.FINEST, "Polynomial constraint simplification took {0} ns.\n", nanosTotal);
        }
        if (finalConstraintsWithMaps == null) {
            if (LimitPOLOSolver.log.isLoggable(Level.FINEST)) {
                LimitPOLOSolver.log.log(Level.FINEST, "SimplePolyConstraintSimplifier has found the constraints to be UNSATISFIABLE for range {0}.\n",
                    this.engine.getRanges().getDefaultValue());
            }
            return null;
        }
        if (LimitPOLOSolver.log.isLoggable(Level.FINEST)) {
            LimitPOLOSolver.log.log(Level.FINEST, "SimplePolyConstraintSimplifier reduced problem by {0} constraints.\n",
                    constraintsNum - finalConstraintsWithMaps.x.size() - finalConstraintsWithMaps.w.size());
        }


        if (this.engine instanceof SatSearch && ((SatSearch) this.engine).isMiniSAT2Incremental()) {


            LimitPOLOSolver.log.log(Level.FINEST,"Entering incremental search.\n");
            SatSearch.IncrementalSearchInstance retInst;
            retInst = ((SatSearch) this.engine).multiSearch(finalConstraintsWithMaps.x, finalConstraintsWithMaps.w, ((SatSearch) this.engine).getConverter(), aborter);

            goalState = retInst.searchFirst();



            Map<String, BigInteger> newGoalState = goalState;

            while(newGoalState != null) {
                LimitPOLOSolver.log.log(Level.FINE, "An incremental instance found a solution.");
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


        activeResolver.specialize(goalState);
        QActiveOrder solvingOrder;
        if (goalState != null) {
            DefaultValueMap<String, BigInteger> refinedGoal = new DefaultValueMap<String, BigInteger>(BigInteger.ZERO);
            refinedGoal.putAll(goalState);

            final LPOLSymbolRepresentations representation =  this.inter.getRepresentations().specialize(refinedGoal);

            LimitPOLOSolver.log.log(Level.FINEST, representation.export(new PLAIN_Util()));



            //if (Globals.useAssertions) {
            final LPOLInterpretor specti = new LPOLInterpretor(representation);



                // Do we really fulfill LimitPOLOO constraints? TODO!
                /*final Map<Term, Matrix> specializedMatrices = new LinkedHashMap<Term, Matrix>();
                for (final Map.Entry<Term, Matrix> entry: termInterpretations.entrySet()) {
                    specializedMatrices.put(entry.getKey(), entry.getValue().specialize(goalState));
                }
                for (final Map.Entry<Constraint<Term>, QActiveCondition> entry : cs.entrySet()) {

                    if (activeResolver.get(entry.getValue())) {
                        if (!this.fact.hasSpecialOrder() && !this.rational) {
                            assert specializedMatrices.get(entry.getKey().getLeft()).isGE(specializedMatrices.get(entry.getKey().getRight()));
                        } else if (this.rational) {
                            // For rational we always have to reinterpret, since depth of the other term is an issue.
                            final Term leftTerm = entry.getKey().getLeft();
                            final Term rightTerm = entry.getKey().getRight();
                            final Matrix l =  specti.interpretTerm(leftTerm, 1, null, leftTerm, rightTerm.getDepth() > leftTerm.getDepth()? -(rightTerm.getDepth() - leftTerm.getDepth()):0);
                            final Matrix r =  specti.interpretTerm(rightTerm, 1, null, rightTerm, leftTerm.getDepth() > rightTerm.getDepth()? -(leftTerm.getDepth() - rightTerm.getDepth()):0);
                            assert this.fact.isGE(l, r);
                        } else {
                            assert this.fact.isGE(specializedMatrices.get(entry.getKey().getLeft()), (specializedMatrices.get(entry.getKey().getRight())));
                        }
                    }
                }
                boolean foundStrict = dpcs.isEmpty();
                for (final Constraint<Term> constraint: dpcs) {
                    final Matrix leftmatrix = specializedMatrices.get(constraint.getLeft());
                    final Matrix rightmatrix = specializedMatrices.get(constraint.getRight());
                    if (!this.fact.hasSpecialOrder() && !this.rational) {
                        assert leftmatrix.isGE(rightmatrix);
                        foundStrict |= leftmatrix.isGT(rightmatrix);
                    } else if (this.rational) {
                        // For rational we always have to reinterpret, since depth of the other term is an issue.
                        final Term leftTerm = constraint.getLeft();
                        final Term rightTerm = constraint.getRight();
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

*/
            solvingOrder = new LimitPOLO(representation);

        } else {
            solvingOrder = null;
        }

        return solvingOrder;

    }


    private Collection<VarPolyConstraint> multiplyAll(final SimplePolynomial polynomial, final Collection< ? extends VarPolyConstraint> constraints) {
        final LinkedHashSet<VarPolyConstraint> result = new LinkedHashSet<VarPolyConstraint>();

        for (final VarPolyConstraint vpc: constraints) {
            result.add (new VarPolyConstraint (vpc.getPolynomial().times(polynomial), vpc.getType()));
        }

        return result;
    }





    private void merge(final Set<SimplePolyConstraint> spcs, final QActiveCondition cond, final Map<QActiveCondition, Set<SimplePolyConstraint>> constraints) {
        if (!constraints.containsKey(cond)) {
            constraints.put(cond, new LinkedHashSet<SimplePolyConstraint>());
        }
        constraints.get(cond).addAll(spcs);

    }



    private <T> Map<T, QActiveCondition> toMap(final Collection<T> constraints, final QActiveCondition value) {
        final Map<T, QActiveCondition> retMap = new LinkedHashMap<T, QActiveCondition>();
        for (final T vpc: constraints) {
            retMap.put(vpc, value);
        }
        return retMap;
    }


    @Deprecated
    public static LimitPOLOSolver createRRR(final MatrixFactory fact2, final SearchAlgorithm searchAlg, final ArgumentInterpretor ai, final SimplificationMode simplificationMode2, final boolean simplifyAll2, final boolean stripExponents2, final Boolean dl, final Boolean newsearchstrict, final Boolean pf, final int range) {

        // deprecated
        /*final MATROSolver solver = new MATROSolver(null, fact2, searchAlg, ai, simplificationMode2, simplifyAll2, stripExponents2, dl, false, newsearchstrict, pf, false);
        solver.range = range;
        return solver;
        */
        return null;

    }



    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs,
        Abortion aborter) throws AbortionException {
        // We do not support RRR at the moment.
        return null;
    }






}

