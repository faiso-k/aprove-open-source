package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Interpolation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Ranking sequence (induces a linear lexicographic ranking)
 *
 * @author marinag
 *
 */
public class LinLexRanking {

    private final ConstraintsSystemSolver consSysSolver;
    private final InterpolationSolver solver;
    private final Abortion aborter;
    private final Map<SimplePolynomial, Integer> positions = new HashMap<>();
    private final List<Pair<SimplePolynomial, LinearTransitionPair>> functions;
    private final String postfix;

    /**
     * @param postfix - variable snapshots suffix tag
     * @param aborter - aborter
     */
    public LinLexRanking(final String postfix, final Abortion aborter) {
        this.functions = new ArrayList<>();

        this.postfix = postfix;
        this.consSysSolver = ConstraintsSystemSolver.create(aborter);
        this.solver = InterpolationSolver.create(null, null, null, aborter);
        this.aborter = aborter;

    }

    @Override
    public String toString() {
        final StringBuilder strBuilder = new StringBuilder();

        for (final Pair<SimplePolynomial, LinearTransitionPair> item : this.functions) {
            strBuilder.append("(");
            if (!item.y.x.isTrue()) {
                strBuilder.append(item.y.x + " ");
            }
            strBuilder.append("max(0," + item.x + ") ");
            strBuilder.append(item.y.y.trim());
            strBuilder.append(")");
        }

        return strBuilder.toString();
    }

    /**
     * @return list of polynomials of this ranking function
     */
    public List<SimplePolynomial> getPolynomials() {
        final List<SimplePolynomial> polys = new ArrayList<>();

        for (final Pair<SimplePolynomial, LinearTransitionPair> f : this.functions) {
            polys.add(f.x);
        }

        return polys;
    }

    /**
     * @return corresponding error condition (i.e. non-satisfaction of the decrease requirement)
     */
    public LinearDisjunction toErrorCondition() {
        return this.toLinearDisjunction().negate();
    }

    /**
     * @return condition representing the decrease requirement of this ranking function
     */
    public LinearDisjunction toLinearDisjunction() {
        final Map<String, String> renamingMap = new HashMap<>();
        for (final SimplePolynomial poly : this.getPolynomials()) {
            for (final String var : poly.getVariables()) {
                if (!renamingMap.containsKey(var)) {
                    renamingMap.put(var, var + this.postfix);
                }
            }
        }

        final Set<LinearConstraintsSystem> constraints = new HashSet<>();
        for (int i = 0; i < this.functions.size(); i++) {
            constraints.add(LinLexRanking.toLinearConstraintsSystem(this.functions.subList(0, i + 1), renamingMap));
        }
        return LinearDisjunction.create(constraints);
    }

    /**
     * @param list - list of rankings
     * @param renamingMap - renaming to snapshots
     * @return sub-requirement of the decrease requirement of this ranking function
     */
    private static LinearConstraintsSystem toLinearConstraintsSystem(
        final List<Pair<SimplePolynomial, LinearTransitionPair>> list,
        final Map<String, String> renamingMap)
    {
        final int i = list.size() - 1;

        final SimplePolynomial fi = list.get(i).x;
        final SimplePolynomial fiPre = fi.replace(renamingMap);

        final Set<SimplePolyConstraint> constraints = new HashSet<>();

        constraints.add(new SimplePolyConstraint(fiPre.minus(fi), ConstraintType.GT));
        constraints.add(new SimplePolyConstraint(fiPre.plus(SimplePolynomial.ONE), ConstraintType.GE));

        for (int j = 0; j < i; j++) {
            final SimplePolynomial fj = list.get(j).x;
            final SimplePolynomial fjPre = fj.replace(renamingMap);

            constraints.add(new SimplePolyConstraint(fjPre.minus(fj), ConstraintType.GE));
        }

        return LinearConstraintsSystem.create(constraints);
    }

    /**
     * @param poly simple polynomial
     * @param cond bound (condition)
     * @return true if poly is bounded given the condition (i.e. cond => (poly >= 0)), false otherwise
     */
    private boolean isBounded(final SimplePolynomial poly, final LinearConstraintsSystem cond) {
        final LinearConstraintsSystem c =
            LinearConstraintsSystem.create(new SimplePolyConstraint(poly, ConstraintType.GE));
        return this.solver.isImplied(cond, c);
    }


    /**
     * @param transition
     * @param stem
     * @param cycle
     * @param list
     * @return
     */
    public Pair<Boolean, List<Edge<LinearTransitionPair, LocationID>>> findOrientingRankingInsert(
        final LinearTransitionPair transition,
        final LinearConstraintsSystem stem,
        final List<Edge<LinearTransitionPair, LocationID>> cycle,
        final List<Edge<LinearTransitionPair, LocationID>> list)
        {

        final Map<Edge<LinearTransitionPair, LocationID>, LinearTransitionPair> cycleRelations = new HashMap<>();
        for (final Edge<LinearTransitionPair, LocationID> edge : cycle) {
            cycleRelations.put(edge, edge.getObject());
        }

        final Set<PolyRelation> context = new HashSet<>();

        boolean singleCycle = true;
        for (final Edge<LinearTransitionPair, LocationID> edge : list) {
            singleCycle =
                singleCycle && cycleRelations.containsKey(edge) && (cycleRelations.get(edge).equals(edge.getObject()));

            context.add(edge.getObject().y);
        }

        final List<Edge<LinearTransitionPair, LocationID>> decreasingEdges = new LinkedList<>();

        if (singleCycle) {
            if (this.insert(stem, transition)) {
                return new Pair<>(true, cycle);
            }
        }

        for (final Edge<LinearTransitionPair, LocationID> e : cycle) {
            if (e.getObject().x.isTrue() || e.getObject().y.isIdentity()) {
                continue;
            }
            if (((CoopLocation) e.getEndNode()).getType().equals(CoopLocationType.CUTPOINT_DUPLICATE)) {
                continue;
            }


            final Set<PolyRelation> unaffect = new HashSet<>();
            unaffect.addAll(context);
            unaffect.remove(e.getObject().y);

            final Set<List<Pair<SimplePolynomial, LinearTransitionPair>>> ls =
                this.getReducing(LinearConstraintsSystem.LIN_TRUE, e.getObject(), unaffect);

            for (final List<Pair<SimplePolynomial, LinearTransitionPair>> rf : ls) {
                if (this.tryInsert(rf)) {
                    decreasingEdges.add(e);
                }
            }
        }

        return new Pair<>(!decreasingEdges.isEmpty(), decreasingEdges);
        }

    /**
     * @param stem
     * @param transition - cycle transition pair
     * @param toDecrease
     * @return true if could find a reducing & bounded ranking for cycle and also insert it in the existing ranking. false, otherwise.
     */
    public boolean insert(
        final LinearConstraintsSystem stem,
        final LinearTransitionPair transition)
    {
        final Set<List<Pair<SimplePolynomial, LinearTransitionPair>>> ls =
            this.getReducing(stem, transition, null);

        while (!ls.isEmpty()) {
            int length = Integer.MAX_VALUE;

            for (final List<Pair<SimplePolynomial, LinearTransitionPair>> item : ls) {
                if (item.size() < length) {
                    length = item.size();
                }
            }

            for (final List<Pair<SimplePolynomial, LinearTransitionPair>> item : new HashSet<>(ls))
            {
                if (item.size() == length) {
                    if (this.tryInsert(item)) {
                        return true;
                    }
                    ls.remove(item);
                }
            }
        }

        return false;
    }

    private Set<Pair<SimplePolynomial, LinearTransitionPair>> getRankingFunctions(
        final LinearTransitionPair relation,
        final Set<SimplePolynomial> toDecrease)
        {
        final Set<Pair<SimplePolynomial, LinearTransitionPair>> result = new HashSet<>();

        for (final SimplePolynomial poly : toDecrease) {
            final Pair<List<SimplePolynomial>, List<SimplePolyConstraint>> ranking =
                this.getRankingPolynomials(relation, poly, new HashSet<SimplePolynomial>());

            if (ranking != null) {
                final Pair<SimplePolynomial, LinearTransitionPair> pair =
                    new Pair<>(SimplePolynomial.ZERO, new LinearTransitionPair(
                        LinearConstraintsSystem.create(ranking.y),
                        relation.y));
                    Collections.reverse(ranking.x);
                    for (final SimplePolynomial p : ranking.x) {
                        pair.x = pair.x.plus(pair.x).plus(p);
                    }
                    result.add(pair);
            }
        }
        return result;
        }

    private Pair<List<SimplePolynomial>, List<SimplePolyConstraint>> getRankingPolynomials(
        final LinearTransitionPair relation,
        final SimplePolynomial poly,
        final HashSet<SimplePolynomial> previous)
        {
        if (previous.contains(poly)) {
            return null;
        }

        final LinearConstraintsSystem C =
            LinearConstraintsSystem.create(new SimplePolyConstraint(poly.negate(), ConstraintType.GT));

        if (this.consSysSolver.implies(relation.x, C)) {
            final SimplePolyConstraint I = this.solver.solve(relation.x, C);

            return new Pair<>(Arrays.asList(poly), Arrays.asList(I));
        }

        if (poly.isConstant()) {
            return null;
        }

        final SimplePolynomial polyDiff = relation.y.apply(poly).minus(poly);

        previous.add(poly);

        final Pair<List<SimplePolynomial>, List<SimplePolyConstraint>> subRanking =
            this.getRankingPolynomials(relation, polyDiff, previous);

        if (subRanking != null) {
            subRanking.x.add(poly);
        }

        return subRanking;

        }

    private boolean tryInsert(final List<Pair<SimplePolynomial, LinearTransitionPair>> ls) {

        final List<Integer> insertPos = new ArrayList<>();

        int from = this.functions.size() - 1;

        for (int i = ls.size() - 1; i >= 0; i--) {
            final int pos = this.getPosition(from, ls.get(i));

            if (pos < 0) {
                return false;
            }

            insertPos.add(0, pos);

            from = pos - 1;
        }

        int offset = 0;

        for (int i = 0; i < ls.size(); i++) {
            final int pos = insertPos.get(i);
            final Pair<SimplePolynomial, LinearTransitionPair> item = ls.get(i);

            final int j = pos + offset;

            if (j < this.functions.size()) {
                final SimplePolynomial diff = this.functions.get(j).x.minus(item.x);

                if (!new SimplePolyConstraint(diff.negate(), ConstraintType.GT).isSatisfiable()) {
                    continue;
                }

                if (diff.isConstant()) {
                    this.functions.remove(j);
                }

            }

            this.functions.add(j, item);

            //            for (final String var : item.x.getVariables()) {
            //                if (!this.renamingMap.containsKey(var)) {
            //                    this.renamingMap.put(var, var + this.postfix);
            //                }
            //            }

            offset++;
        }

        return (offset > 0);
    }

    private int getPosition(final int from, final Pair<SimplePolynomial, LinearTransitionPair> pair) {

        if (this.getPolynomials().contains(pair.x)) {
            final int position = this.getPolynomials().indexOf(pair.x);

            if (position >= from) {
                return position;
            }

            return -1;
        }

        if (from < 0) {
            return 0;
        }

        if (this.isUnchanged(this.functions.get(from).y, pair.x)) { // replacing isUnchanged
            return this.getPosition(from - 1, pair);
        }

        // No choice left, must insert here. Make sure we don't change the others..

        for (int i = from; i < this.functions.size(); i++) {
            if (!this.isUnchanged(pair.y, this.functions.get(i).x)) {
                return -1;
            }
        }

        return from;
    }

    /**
     * @param PolyRelation
     * @param bound
     * @param poly
     * @param type
     * @return
     */
    private boolean compare(
        final LinearTransitionPair tp,
        final SimplePolynomial poly,
        final ConstraintType type)
    {
        final SimplePolynomial polyP = (tp.y.apply(poly));

        if (polyP == null) {
            return false;
        }

        final SimplePolynomial diff = polyP.minus(poly);

        final SimplePolyConstraint c = new SimplePolyConstraint(diff, type);

        if (!c.isSatisfiable()) {
            return true;
        }

        if (c.isSatisfiable() && c.getPolynomial().isConstant()) {
            return false;
        }

        final SimplePolyConstraint interpolant = this.solver.solve(tp.x, LinearConstraintsSystem.create(c));

        if (interpolant != null && interpolant.isSatisfiable()) {
            return true;
        }

        return false;
    }

    /**
     * @param relation relation
     * @param bound bound (condition)
     * @param poly simple polynomial
     * @return true if poly is not increased by applying relation
     */
    public boolean isNotIncreased(
        final LinearTransitionPair tp,
        final SimplePolynomial poly)
    {
        return this.compare(tp, poly, ConstraintType.GT);
    }

    /**
     * @param tp relation
     * @param bound bound (condition)
     * @param poly simple polynomial
     * @return true if poly is  decreased by applying relation
     */
    boolean isDecreased(final LinearTransitionPair tp, final SimplePolynomial poly) {
        return this.compare(tp, poly, ConstraintType.GE);
    }


    /**
     * @param relation relation
     * @param bound bound (condition)
     * @param poly simple polynomial
     * @return true if poly is unchanged by applying relation
     */
    private boolean isUnchanged(
        final LinearTransitionPair tp,
        final SimplePolynomial poly)
    {
        return this.compare(tp, poly, ConstraintType.GT) || this.compare(tp, poly.negate(), ConstraintType.GT);
    }


    /**
     * @param transition cycle transition pair
     * @return set of possible lexicographic ranking sequences for given cycle and stem bound
     */
    public Set<List<Pair<SimplePolynomial, LinearTransitionPair>>> getReducing_(
        final LinearTransitionPair transition,
        final Set<SimplePolynomial> toDecrease)
        {
        final Set<List<Pair<SimplePolynomial, LinearTransitionPair>>> rfs = new HashSet<>();

        for (final SimplePolynomial p : toDecrease) {
            final List<Pair<SimplePolynomial, LinearTransitionPair>> rf =
                this.getReducing(p, transition, new ArrayList<SimplePolynomial>());

            if (rf != null) {
                rfs.add(rf);
            }
        }

        return rfs;
        }

    private static VarPolynomial simplePolyToVarPoly(final SimplePolynomial poly) {
        final Map<IndefinitePart, SimplePolynomial> varMon = new HashMap<>();
        for (final Entry<IndefinitePart, BigInteger> p : poly.getSimpleMonomials().entrySet()) {
            varMon.put(p.getKey(), SimplePolynomial.create(p.getValue()));
        }

        return VarPolynomial.create(ImmutableCreator.create(varMon));
    }

    private static SimplePolynomial varPolyToSimplePoly(final VarPolynomial vp) {
        final Set<SimplePolynomial> simplePolys = new HashSet<>();
        for (final Entry<IndefinitePart, SimplePolynomial> p : vp.getVarMonomials().entrySet()) {
            simplePolys.add(p.getValue().times(p.getKey()));
        }

        return SimplePolynomial.plus(simplePolys);
    }

    public Set<List<Pair<SimplePolynomial, LinearTransitionPair>>> getReducing(
        final LinearConstraintsSystem stem,
        final LinearTransitionPair transition,
        final Set<PolyRelation> unaffected)
        {

        final Set<List<Pair<SimplePolynomial, LinearTransitionPair>>> rfs = new HashSet<>();

        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);

        final PolyRelation A = transition.y;

        final List<Pair<String, SimplePolynomial>> bPairs = new ArrayList<>();

        final Set<String> detVars = transition.y.getVariablesNames();

        for (final Pair<String, SimplePolynomial> p : A.getTransitions()) {
            if (p.getKey().contains("^")) { //|| p.y == null) {
                continue;
            }

            final SimplePolynomial pD =
                p.y == null ? SimplePolynomial.create(ng.getFreshName("w", false)) : p.y.minus(SimplePolynomial
                    .create(p.x));

                bPairs.add(new Pair<>(p.getKey(), pD));
        }


        final PolyRelation B = PolyRelation.createRelation(bPairs);

        final Map<IndefinitePart, SimplePolynomial> stemCond = new HashMap<>();
        final Map<IndefinitePart, SimplePolynomial> loopCond = new HashMap<>();

        final Map<IndefinitePart, SimplePolynomial> unaffectCond = new HashMap<>();

        final Set<SimplePolyConstraint> stemConstraints = new HashSet<>();
        stemConstraints.addAll(stem.getConstraints());
        if (unaffected == null || unaffected.isEmpty()) {
            stemConstraints.addAll(transition.x.getConstraints());
        }

        for (final SimplePolyConstraint c : stemConstraints) {
            if (transition.x.contains(c)) {
                // continue;
            }
            stemCond.put(
                IndefinitePart.create(ng.getFreshName("a", false), 1),
                c.getPolynomial());

            if (c.getType().equals(ConstraintType.EQ)) {
                stemCond.put(
                    IndefinitePart.create(ng.getFreshName("a", false), 1),
                    c.getPolynomial().negate());
            }
        }

        for (final SimplePolyConstraint c : transition.getKey().getConstraints()) {

            final SimplePolynomial p = c.getPolynomial();

            if (!detVars.containsAll(p.getVariables())) {
                continue;
            }

            if (loopCond.containsKey(p)) {
                continue;
            }

            if (transition.y.apply(p) == null) {
                //continue;
            }

            loopCond.put(IndefinitePart.create(ng.getFreshName("b", false), 1), p);


            if (c.getType().equals(ConstraintType.EQ) && !loopCond.values().contains(c.getPolynomial().negate())) {
                loopCond.put(IndefinitePart.create(ng.getFreshName("b", false), 1), c.getPolynomial().negate());
            }
        }


        final Set<SimplePolyConstraint> basicConstraints = new HashSet<>();

        for (final IndefinitePart v : stemCond.keySet()) {
            basicConstraints
            .add(new SimplePolyConstraint(SimplePolynomial.create(v, BigInteger.ONE), ConstraintType.GE));
        }

        final Set<SimplePolynomial> loopCoefs = new HashSet<>();


        for (final IndefinitePart v : loopCond.keySet()) {
            final SimplePolynomial p = SimplePolynomial.create(v,BigInteger.ONE);
            basicConstraints.add(new SimplePolyConstraint(p, ConstraintType.GE));
            loopCoefs.add(p);
        }

        final Map<String, IndefinitePart> varCoefs = new HashMap<>();

        final ArrayList<PolyRelation> Bs = new ArrayList<>();

        final ArrayList<PolyRelation> As = new ArrayList<>();

        final VarPolynomial stemP = VarPolynomial.create(ImmutableCreator.create(stemCond));
        final VarPolynomial loopP = VarPolynomial.create(ImmutableCreator.create(loopCond));

        for (final String coef : loopP.getCoefficients()) {
            if (coef.startsWith("y")) {
                continue;
            }

            final SimplePolynomial poly = LinLexRanking.getSumOfCoefs(loopP, coef);

            if (poly.isZero()) {
                continue;
            }

            final ConstraintType type = ConstraintType.EQ;

            basicConstraints.add(new SimplePolyConstraint(poly, type));
        }

        Log.report("stemVars", stemCond.toString());
        Log.report("loopVars", loopCond.toString());

        int prevRank;

        PolyRelation Bn = B;

        PolyRelation An = A;

        int iter = B.getVariablesNames().size();

        final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);

        if (unaffected != null) {
            for (final PolyRelation r : unaffected) {
                final VarPolynomial diff = loopP.minus(r.apply(loopP));

                final SimplePolynomial p = LinLexRanking.getSumOfCoefs(diff);
                basicConstraints.add(new SimplePolyConstraint(p, ConstraintType.EQ));

                for (final String coef : diff.getCoefficients()) {
                    final SimplePolynomial poly = LinLexRanking.getSumOfCoefs(diff, coef);

                    if (poly.isZero()) {
                        continue;
                    }

                    basicConstraints.add(new SimplePolyConstraint(poly, ConstraintType.EQ));
                }
            }
        }


        do {

            prevRank = Bn.getRank();

            Bs.add(Bn);

            As.add(An);

            final VarPolynomial loopPn = Bn.apply(loopP);

            final VarPolynomial sumPn = stemP.plus(loopPn);



            Log.report("sumPn", iter + ") " + sumPn.toString() + "\t" + Bn);


            final Set<SimplePolyConstraint> constraints = new HashSet<>();

            for (final String coef : sumPn.getCoefficients()) {
                if (coef.startsWith("y")) {
                    continue;
                }

                final SimplePolynomial poly = LinLexRanking.getSumOfCoefs(sumPn, coef);

                if (poly.isZero()) {
                    continue;
                }

                final ConstraintType type = ConstraintType.EQ;

                basicConstraints.add(new SimplePolyConstraint(poly, type));
            }

            for (final String coef : sumPn.getCoefficients()) {
                final SimplePolynomial poly = LinLexRanking.getSumOfCoefs(sumPn, coef);

                if (poly.isZero()) {
                    continue;
                }

                final ConstraintType type = ConstraintType.EQ;


                constraints.add(new SimplePolyConstraint(poly, type));
            }

            constraints.add(new SimplePolyConstraint(
                LinLexRanking.getSumOfCoefs(sumPn).plus(SimplePolynomial.ONE).negate(),
                ConstraintType.GE));

            constraints.addAll(basicConstraints);

            final LinearConstraintsSystem consSys = LinearConstraintsSystem.create(constraints);

            final ImmutableMap<String, BigInteger> solution = this.consSysSolver.solve(consSys);

            if (solution != null) {
                Log.report("valuation", solution.toString());
                final Map<String, Integer> valuation = new HashMap<>();

                BigInteger gcd = null;

                for (final Entry<String, BigInteger> p : solution.entrySet()) {
                    if (gcd == null) {
                        gcd = p.getValue();
                    } else {
                        gcd = gcd.gcd(p.getValue());
                    }
                }

                for (final Entry<String, BigInteger> p : solution.entrySet()) {
                    valuation.put(p.getKey(), p.getValue().divide(gcd).intValue());
                }

                final SimplePolynomial loopPval = loopP.evaluate(valuation);
                final SimplePolynomial stemPval = stemP.evaluate(valuation);

                final LinearTransitionPair tp = new LinearTransitionPair(transition.x.merge(stem), transition.y, true);

                List<Pair<SimplePolynomial, LinearTransitionPair>> ls = new ArrayList<>();

                ls.add(new Pair<>(loopPval, new LinearTransitionPair(LinearConstraintsSystem.LIN_TRUE, transition.y
                    .restrict(loopPval.getVariables()), true)));

                final Set<String> variables = new HashSet<>();

                for (int i = 0; i < Bs.size(); i++) {

                    if (this.isDecreased(tp, ls.get(ls.size() - 1).x)) {
                        break;
                    }

                    final PolyRelation R = Bs.get(i);
                    final SimplePolynomial loopPvaln = R.apply(loopPval);

                    final Set<String> vars = loopPvaln.getVariables();

                    if (vars.isEmpty()) {
                        continue;
                    }

                    ls.add(new Pair<>(loopPvaln, new LinearTransitionPair(LinearConstraintsSystem.LIN_TRUE,
                        A.restrict(vars),
                        true)));
                }

                Collections.reverse(ls);



                if (transition.y.apply(ls.get(0).x).equals(ls.get(0).x)) {
                    if (ls.size() <= 1) {
                        continue;
                    }
                    ls = ls.subList(1, ls.size());

                }
                if (!stemPval.isConstant()) {
                    ls.get(0).y.x =
                        LinearConstraintsSystem.create(new SimplePolyConstraint(stemPval, ConstraintType.GE));
                }

                if (this.isDecreased(tp, ls.get(0).x)) {
                    rfs.add(ls);
                    return rfs;
                }

            }

            if (unaffected != null && !unaffected.isEmpty()) {
                break;
            }

            Bn = PolyRelation.compose(B, Bn);
            An = PolyRelation.compose(A, An);

            Log.report("rel", Bn.toString());

            iter--;

        } while (Bn.getRank() < prevRank);

        return rfs;

        }

    private static SimplePolynomial getSumOfCoefs(final VarPolynomial vp, final String coefVar) {
        final Set<SimplePolynomial> polys = new HashSet<>();

        for (final Entry<IndefinitePart, SimplePolynomial> p : vp.getVarMonomials().entrySet()) {
            assert p.getValue().isLinear();

            for (final Entry<IndefinitePart, BigInteger> m : p.getValue().getSimpleMonomials().entrySet()) {
                if (m.getKey().contains(coefVar)) {
                    polys.add(SimplePolynomial.create(p.getKey(), m.getValue()));
                }
            }
        }

        return SimplePolynomial.plus(polys);
    }

    private static SimplePolynomial getSumOfCoefs(final VarPolynomial vp) {
        final Set<SimplePolynomial> polys = new HashSet<>();
        final IndefinitePart indef = IndefinitePart.ONE;

        for (final Entry<IndefinitePart, SimplePolynomial> p : vp.getVarMonomials().entrySet()) {
            assert p.getValue().isLinear();

            if (p.getValue().getSimpleMonomials().containsKey(indef)) {
                polys.add(SimplePolynomial.create(p.getKey(), p.getValue().getSimpleMonomials().get(indef)));
            }
        }

        return SimplePolynomial.plus(polys);
    }

    /**
     * @param transition
     * @param bound
     * @return
     */
    public Set<SimplePolynomial> getLocalyReducing(
        final LinearTransitionPair transition,
        final LinearConstraintsSystem bound)
        {

        final Set<SimplePolynomial> rf = new HashSet<>();

        for (final SimplePolyConstraint constraint : transition.x.getConstraints())
        {
            final SimplePolynomial poly = constraint.getPolynomial();
            final SimplePolynomial polyP = (transition.y.apply(poly));

            if (polyP == null) {
                continue;
            }

            final SimplePolynomial diff = poly.minus(polyP);

            final SimplePolyConstraint c = new SimplePolyConstraint(diff.negate(), ConstraintType.GE);

            if (!c.isSatisfiable()) {
                rf.add(poly);
                continue;
            }

            final SimplePolyConstraint interpolant = this.solver.solve(bound, LinearConstraintsSystem.create(c));

            if (interpolant != null && interpolant.isSatisfiable()) {
                rf.add(poly);
            }

        }

        return rf;
        }

    /**
     * @param poly simple polynomial
     * @param transition cycle transition pair
     * @param bound stem bound (condition)
     * @param previous previously processed polynomials (to assure termination)
     * @return sequence of ranking triples reducing poly, of such could be found. null otherwise.
     */
    public List<Pair<SimplePolynomial, LinearTransitionPair>> getReducing(
        final SimplePolynomial poly,
        final LinearTransitionPair transition,
        final List<SimplePolynomial> previous)
        {

        if (previous.contains(poly)) {
            return null;
        }

        previous.add(poly);

        final List<Pair<SimplePolynomial, LinearTransitionPair>> rf = new ArrayList<>();

        final SimplePolynomial polyP = (transition.y.apply(poly));

        if (polyP == null) {
            return null;
        }

        final SimplePolyConstraint cP = new SimplePolyConstraint(polyP, ConstraintType.GE);

        if (!cP.isSatisfiable()) {
            final PolyRelation r = transition.y.restrict(poly.getVariables());
            rf.add(new Pair<>(poly, new LinearTransitionPair(LinearConstraintsSystem.LIN_TRUE, r)));
            return rf;
        }

        final Set<String> preVars = poly.getVariables();
        final Set<String> postVars = polyP.getVariables();

        postVars.retainAll(preVars);

        if (postVars.isEmpty()) {
            final List<Pair<SimplePolynomial, LinearTransitionPair>> subRf =
                this.getReducing(
                    polyP,
                    new LinearTransitionPair(transition.x, transition.y.restrict(polyP.getVariables())),
                    previous);

            if (subRf != null) {
                rf.addAll(subRf);
                final PolyRelation r = transition.y.restrict(poly.getVariables());
                rf.add(new Pair<>(poly, new LinearTransitionPair(LinearConstraintsSystem.LIN_TRUE, r)));
                return rf;
            }
        }


        final SimplePolynomial diff = polyP.minus(poly);
        final SimplePolyConstraint c = new SimplePolyConstraint(diff, ConstraintType.GE);

        if (!c.isSatisfiable()) {
            final PolyRelation r = transition.y.restrict(poly.getVariables());
            rf.add(new Pair<>(poly, new LinearTransitionPair(LinearConstraintsSystem.LIN_TRUE, r)));
            return rf;
        }

        if (c.isSatisfiable() && c.getPolynomial().isConstant()) {
            return null;
        }

        final SimplePolyConstraint interpolant =
            this.solver.solve(transition.x, LinearConstraintsSystem.create(c));

        if (interpolant != null && interpolant.isSatisfiable()) {
            final PolyRelation r = transition.y.restrict(poly.getVariables());

            if (interpolant.getPolynomial().isConstant()) {
                rf.add(new Pair<>(poly.negate(), new LinearTransitionPair(
                    LinearConstraintsSystem.create(interpolant),
                    r)));
            } else {
                rf.add(new Pair<>(poly, new LinearTransitionPair(LinearConstraintsSystem.create(interpolant), r)));
            }

            return rf;
        }

        if (diff.isZero()
            || this.isNotIncreased(transition, poly.negate()))
        {
            return null;
        }

        if (poly.plus(polyP).isConstant()) {
            return null;
        }

        final PolyRelation subRel = transition.y;

        if (subRel.isIdentity()) {
            return null;
        }

        final LinearConstraintsSystem consSysB =
            LinearConstraintsSystem.create(new SimplePolyConstraint(diff.negate(), ConstraintType.GE));
        final SimplePolyConstraint interpolantB = this.solver.solve(transition.x, consSysB);

        if (interpolantB != null && interpolantB.isSatisfiable()) {
            return null;
        }

        final List<Pair<SimplePolynomial, LinearTransitionPair>> subRf =
            this.getReducing(diff, new LinearTransitionPair(transition.x, subRel), previous);

        if (subRf != null) {
            rf.addAll(subRf);
            final PolyRelation r = transition.y.restrict(poly.getVariables());
            rf.add(new Pair<>(poly, new LinearTransitionPair(LinearConstraintsSystem.LIN_TRUE, r)));
            return rf;
        }

        return null;
        }

    private Set<List<Pair<SimplePolynomial, LinearTransitionPair>>> getReducing(
        final PolyRelation cyclePolyRelation,
        final Set<SimplePolynomial> toDecrease,
        final List<Edge<LinearTransitionPair, LocationID>> cycle,
        final LinearConstraintsSystem bound)
        {

        final Set<List<Pair<SimplePolynomial, LinearTransitionPair>>> reducing = new HashSet<>();

        for (final SimplePolynomial poly : toDecrease) {
            if (!this.isDecreased(new LinearTransitionPair(bound, cyclePolyRelation), poly)) {
                continue;
            }

            final List<Pair<SimplePolynomial, LinearTransitionPair>> rf =
                this.getReducing(poly, cycle, bound, new HashSet<SimplePolynomial>());
            if (rf != null) {
                reducing.add(rf);
            }
        }

        return reducing;

        }

    private List<Pair<SimplePolynomial, LinearTransitionPair>> getReducing(
        final SimplePolynomial poly,
        final List<Edge<LinearTransitionPair, LocationID>> cycle,
        final LinearConstraintsSystem bound,
        final Set<SimplePolynomial> previous)
        {

        if (previous.contains(poly)) {
            return null;
        }

        for (final Edge<LinearTransitionPair, LocationID> e : cycle) {
            final PolyRelation r = e.getObject().y;

            if (r.isIdentity()) {
                continue;
            }

            final LinearConstraintsSystem c = (e.getObject().x);

            if (this.isDecreased(e.getObject(), poly)) {
                final List<Pair<SimplePolynomial, LinearTransitionPair>> rf = new LinkedList<>();
                rf.add(new Pair<>(poly, new LinearTransitionPair(bound, r.restrict(poly.getVariables()))));
                return rf;
            }

            final List<Pair<SimplePolynomial, LinearTransitionPair>> rf = new ArrayList<>();

            final SimplePolynomial polyP = (r.apply(poly));

            if (polyP == null) {
                continue;
            }

            if (polyP.isConstant()) {
                if (polyP.getNumericalAddend().compareTo(BigInteger.ZERO) < 0) {
                    rf.add(new Pair<SimplePolynomial, LinearTransitionPair>(poly, new LinearTransitionPair(bound, r
                        .restrict(poly.getVariables()))));
                    return rf;
                } else {
                    return null;
                }
            }

            final SimplePolynomial diff = polyP.minus(poly);

            if (diff.isZero() || this.isNotIncreased(new LinearTransitionPair(bound, r), poly.negate())) {
                return null;
            }

            if (poly.plus(polyP).isConstant()) {
                return null;
            }

            final Set<SimplePolynomial> subPrevious = new HashSet<>(previous);

            subPrevious.add(poly);

            final List<Pair<SimplePolynomial, LinearTransitionPair>> subRf =
                this.getReducing(diff, cycle, bound, subPrevious);

            if (subRf != null) {
                subRf.add(new Pair<>(poly, new LinearTransitionPair(bound, r.restrict(poly.getVariables()))));
                return subRf;
            }
        }

        return null;
        }


    /**
     * @param pair transition pair
     * @return true if transition pair is (both bounded and) decreasing w.r.t. to this lex. ranking. false otherwise.
     */
    public boolean isBoundedAndDecreasing(final LinearTransitionPair pair) {
        int i = this.functions.size() - 1;
        final LinearConstraintsSystem bound = (pair.x);

        for (; i >= 0; i--) {
            if (this.isBounded(this.functions.get(i).x, bound)) {
                break;
            }
        }

        for (; i >= 0; i--) {
            if (this.isDecreased(pair, this.functions.get(i).x)) {
                return true;
            }
        }
        return false;
    }

    public boolean isDecreasing(final LinearTransitionPair tp) {
        for (int i = 0; i < this.functions.size(); i++) {
            final SimplePolynomial p = this.functions.get(i).x;
            if (this.isBounded(p, tp.x) && this.isDecreased(tp, p)) {
                return true;
            }

            if (!this.isUnchanged(tp, p)) {
                return false;
            }
        }

        return false;
    }


}
