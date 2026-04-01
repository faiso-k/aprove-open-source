package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.input.Programs.impact.GTP.nodes.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Constraints system solver, keeps track of previously found results
 * @author marinag
 */
public class ConstraintsSystemSolver {

    private final SMTEngine SMT_ENGINE = new SMTLIBEngine();

    /**
     *
     */
    private final Abortion aborter;

    /**
     * Create new empty solver
     */
    private ConstraintsSystemSolver(final Abortion aborter) {
        this.aborter = aborter;
    }

    /**
     * @return new empty solver
     */
    public static ConstraintsSystemSolver create(final Abortion aborter) {
        return new ConstraintsSystemSolver(aborter);
    }

    /**
     * @param consSys collection of constraints systems
     * @return true if the conjunction of the given constraints is SAT, false otherwise
     */
    public boolean isSAT(final Collection<PolyConstraintsSystem> consSys) {
        PolyConstraintsSystem conj = PolyConstraintsSystem.TRUE;

        for (final PolyConstraintsSystem constraint : consSys) {
            conj = this.conjunction(conj, constraint);

            if (conj.isFalse()) {
                return false;
            }
        }

        return true; //isSAT(conj);
    }

    /**
     * @param consSys constraints system
     * @param commonVars set of variable names
     * @return constraint system with only the constraints that depend on at least one of the specified variables
     */
    public synchronized PolyConstraintsSystem restrictVariables(
        final PolyConstraintsSystem consSys,
        final Set<String> commonVars)
    {
        final HashSet<String> totalVars = new HashSet<>();

        final ArrayList<SimplePolyConstraint> cons = new ArrayList<>();

        for (final SimplePolyConstraint p : consSys.getConstraints()) {
            final Set<String> vars = p.getPolynomial().getVariables();
            vars.retainAll(commonVars);

            if (!vars.isEmpty()) {
                cons.add(p);
                totalVars.addAll(vars);
            }
        }
        PolyConstraintsSystem result = PolyConstraintsSystem.create(cons);
        if (!totalVars.containsAll(commonVars)) {
            result = this.restrictVariables(result, totalVars);

        }
        return result;
    }

    /**
     * Solve constraints system
     * @param consSys constraints system
     * @return solution map if exists, null otherwise
     */
    public ImmutableMap<String, BigInteger> solve(final PolyConstraintsSystem consSys) {
        if (consSys.isFalse()) {
            return null;
        }

        if (consSys.getVariables().isEmpty()) {
            return ImmutableCreator.create(new HashMap<String, BigInteger>());
        }

        final Map<String, String> renamingMap = new HashMap<>();
        final PolyConstraintsSystem consSysRenamed = this.createGeneral(consSys, renamingMap);

        if (this.SAT.containsKey(consSysRenamed) && this.SAT.get(consSysRenamed).equals(YNM.NO)) {
            return null;
        }

        if (!this.SOLUTIONS.containsKey(consSysRenamed)) {
            for (final Entry<PolyConstraintsSystem, ImmutableMap<String, BigInteger>> pair : this.SOLUTIONS.entrySet())
            {
                if (consSysRenamed.getConstraints().containsAll(pair.getKey().getConstraints())
                    && pair.getValue() == null)
                {
                    return null;
                }
            }
            Pair<YNM, Map<String, String>> answer;
            try {
                answer = this.SMT_ENGINE.solve(consSysRenamed.getFormulas(), SMTLogic.QF_NIA, this.aborter);
            } catch (final AbortionException e) {
                throw e;
            } catch (final WrongLogicException e) {
                return null;
            }

            final YNM sat = answer.x;
            this.SAT.put(consSysRenamed, sat);

            if (sat.equals(YNM.NO)) {
                this.SOLUTIONS.put(consSysRenamed, null);
            }

            if (!sat.equals(YNM.YES) || answer.y == null) {
                return null;
            }

            final Map<String, BigInteger> result = new HashMap<>();
            for (final Entry<String, String> entry : answer.y.entrySet()) {
                final BigInteger coef = new BigInteger(entry.getValue());
                result.put(entry.getKey(), coef);
            }
            this.SOLUTIONS.put(consSysRenamed, ImmutableCreator.create(result));
        }

        final ImmutableMap<String, BigInteger> renamedSolution = this.SOLUTIONS.get(consSysRenamed);
        if (renamedSolution == null) {
            return null;
        }
        final Map<String, BigInteger> resultR = new HashMap<>();

        for (final Entry<String, String> v : renamingMap.entrySet()) {
            resultR.put(v.getKey(), renamedSolution.get(v.getValue()));
        }

        return ImmutableCreator.create(resultR);
    }

    /**
     * @param consSys constraints system
     * @param renameMap renaming map
     * @return renamed version on sonsSys system
     */
    private
    PolyConstraintsSystem
    createGeneral(final PolyConstraintsSystem consSys, final Map<String, String> renameMap)
    {
        final Set<SimplePolyConstraint> constraints = new HashSet<>();
        final List<String> variables = new ArrayList<>(consSys.getVariables());
        Collections.sort(variables);

        int id = renameMap.keySet().size();
        for (final String v : variables) {
            if (renameMap.containsKey(v)) {
                continue;
            }
            renameMap.put(v, "x" + String.valueOf(id++));
        }

        for (final SimplePolyConstraint c : consSys.toSet()) {
            if (!c.isSatisfiable()) {
                return PolyConstraintsSystem.FALSE;
            }
            constraints.add(new SimplePolyConstraint(c.getPolynomial().replace(renameMap), c.getType()));
        }
        final PolyConstraintsSystem renamed = PolyConstraintsSystem.create(constraints);
        return renamed;
    }

    /**
     * @param consSys constraints system
     * @return check sat result
     */
    private YNM checkSat(final PolyConstraintsSystem consSys) {
        final PolyConstraintsSystem renamed = this.createGeneral(consSys, new HashMap<String, String>());

        if (!this.SAT.containsKey(renamed)) {
            YNM result = null;

            if (consSys.isFalse() || !consSys.constraitsSat()) {
                result = YNM.NO;
            } else if (consSys.getConstraints().size() == 1) {
                result = consSys.getConstraints().get(0).isSatisfiable() ? YNM.YES : YNM.NO;
            } else {
                for (final Entry<PolyConstraintsSystem, YNM> pair : new HashSet<>(this.SAT.entrySet())) {
                    if (pair.getValue().equals(YNM.YES)
                        && pair.getKey().getConstraints().containsAll(renamed.getConstraints()))
                    {
                        result = YNM.YES;
                        break;
                    } else if (pair.getValue().equals(YNM.NO)
                        && renamed.getConstraints().containsAll(pair.getKey().getConstraints()))
                    {
                        result = YNM.NO;
                        break;
                    }
                }
            }

            if (result == null) {
                try {
                    result = this.SMT_ENGINE.satisfiable(renamed.getFormulas(), SMTLogic.QF_NIA, this.aborter);
                } catch (final AbortionException e) {
                    throw e;
                } catch (final WrongLogicException e) {
                    return YNM.MAYBE;
                }
            }

            this.SAT.put(renamed, result);
        }
        return this.SAT.get(renamed);
    }

    /**
     * @param consSys constraints system
     * @return true if could be proved to be SAT, false otherwise
     */
    public boolean isSAT(final PolyConstraintsSystem consSys) {
        if (consSys.isFalse()) {
            return false;
        } else if (consSys.isTrue()) {
            return true;
        } else {
            return this.checkSat(consSys).equals(YNM.YES);
        }
    }

    /**
     * @param consSys constraints system
     * @return true if could be proved to be UNSAT, false otherwise
     */
    public boolean isUNSAT(final PolyConstraintsSystem consSys) {
        if (consSys.isFalse()) {
            return true;
        } else if (consSys.isTrue()) {
            return false;
        } else {
            return this.checkSat(consSys).equals(YNM.NO);
        }
    }

    /**
     * @param a constraints system
     * @param b constraints system
     * @return true if a implies b, false otherwise
     */
    public boolean checkImplication(final PolyConstraintsSystem a, final PolyConstraintsSystem b) {
        final Map<String, String> renameMap = new HashMap<>();
        final PolyConstraintsSystem aR = this.createGeneral(a, renameMap);
        final PolyConstraintsSystem bR = this.createGeneral(b, renameMap);

        final Pair<PolyConstraintsSystem, PolyConstraintsSystem> pair = new Pair<>(aR, bR);

        if (!ConstraintsSystemSolver.IMPLIES_MAP.containsKey(pair)) {
            Boolean result = null;
            if (a.equals(b) || a.isFalse() || a.contains(b)) {
                result = true;
            } else if (a.isTrue()) {
                result = b.isTrue();
            } else if (b.isFalse()) {
                return a.isFalse();
            }

            if (result == null) {
                result = true;
                for (final PolyConstraintsSystem c : bR.negate().getConstraintsSystems()) { //.getConstraints()) {
                    final HashSet<SimplePolyConstraint> constraints = aR.toSet();
                    constraints.addAll(c.toSet());

                    if (!this.isUNSAT(PolyConstraintsSystem.create(constraints))) {
                        result = false;
                        break;
                    }
                }
            }

            if (result) {
                Log.report("IMP", a + " => " + b);
            }

            ConstraintsSystemSolver.IMPLIES_MAP.put(pair, result);
        }
        return ConstraintsSystemSolver.IMPLIES_MAP.get(pair);
    }

    /**
     * @param a polynomial constraint
     * @param b polynomial constraint
     * @return true is a implies b, false otherwise
     */
    boolean implies(final SimplePolyConstraint a, final SimplePolyConstraint b) {
        if (a.equals(b) || !a.isSatisfiable()) {
            return true;
        }


        final SimplePolynomial polyA = a.getPolynomial();
        final SimplePolynomial polyB = b.getPolynomial();

        if (a.getType().equals(ConstraintType.GE) && b.getType().equals(ConstraintType.GE)) {
            final Set<String> variables = a.getPolynomial().getVariables();
            variables.retainAll(b.getPolynomial().getVariables());

            if (variables.isEmpty()) {
                return polyB.isConstant() && b.isSatisfiable();
            }
        }

        final SimplePolynomial polyC = polyA.minus(polyB);
        return polyC.isConstant() && polyC.getNumericalAddend().compareTo(BigInteger.ZERO) <= 0;
    }

    /**
     * @param a first polynomial constraint
     * @param b second polynomial constraint
     * @return true if could determine that a contradicts b, false otherwise
     */
    static boolean contradict(final SimplePolyConstraint a, final SimplePolyConstraint b) {
        if (a.equals(b) || !a.getType().equals(ConstraintType.GE) || !b.getType().equals(ConstraintType.GE)) {
            return false;
        }

        final SimplePolynomial polyC = a.getPolynomial().plus(b.getPolynomial());
        return !(new SimplePolyConstraint(polyC, ConstraintType.GE)).isSatisfiable();
    }

    /**
     * @return set of lower bounded variable
     */
    public HashSet<String> variablesLowBound(final PolyConstraintsSystem a) {
        final HashSet<String> vars = new HashSet<>();

        for (final SimplePolyConstraint cons : a.getConstraints()) {
            final SimplePolynomial poly = cons.getPolynomial();
            for (final IndefinitePart indef : poly.getSimpleMonomials().keySet()) {
                for (final String var : indef.getExponents().keySet()) {
                    if (indef.getExponents().get(var) > 1
                        || poly.getSimpleMonomials().get(indef).compareTo(BigInteger.ZERO) > 0)
                    {
                        vars.add(var);
                    }
                }
            }
        }

        return vars;
    }

    /**
     * @return set of upper bounded variables
     */
    public HashSet<String> variablesUpBound(final PolyConstraintsSystem a) {
        final HashSet<String> vars = new HashSet<>();

        for (final SimplePolyConstraint cons : a.getConstraints()) {
            final SimplePolynomial poly = cons.getPolynomial();
            for (final IndefinitePart indef : poly.getSimpleMonomials().keySet()) {
                for (final String var : indef.getExponents().keySet()) {
                    if (indef.getExponents().get(var) > 1
                        || poly.getSimpleMonomials().get(indef).compareTo(BigInteger.ZERO) < 0)
                    {
                        vars.add(var);
                    }
                }
            }
        }

        return vars;
    }

    /**
     * @param a constraints system
     * @param b constraints system
     * @param aborter aborter
     * @return conjunction constraints system of a and b
     */
    public synchronized PolyConstraintsSystem conjunction(final PolyConstraintsSystem a, final PolyConstraintsSystem b)
    {
        if (this.isUNSAT(a) || this.isUNSAT(b)) {
            return PolyConstraintsSystem.FALSE;
        }

        if (a.contains(b)) {
            return a;
        }

        if (b.contains(a)) {
            return b;
        }

        final Set<SimplePolyConstraint> cons = new HashSet<>();
        cons.addAll(a.getConstraints());
        cons.addAll(b.getConstraints());

        final HashSet<String> variables = new HashSet<>();
        variables.addAll(a.getVariables());
        variables.retainAll(b.getVariables());

        if (variables.isEmpty()) {
            return PolyConstraintsSystem.create(cons);
        }

        final Pair<PolyConstraintsSystem, PolyConstraintsSystem> pairA = new Pair<>(a, b);
        final Pair<PolyConstraintsSystem, PolyConstraintsSystem> pairB = new Pair<>(b, a);

        if (this.CONJUNCTION.containsKey(pairA)) {
            final PolyConstraintsSystem result = this.CONJUNCTION.get(pairA);
            return result;
        } else if (this.CONJUNCTION.containsKey(pairB)) {
            final PolyConstraintsSystem result = this.CONJUNCTION.get(pairB);
            return result;
        }

        for (final Entry<Pair<PolyConstraintsSystem, PolyConstraintsSystem>, PolyConstraintsSystem> p : this.CONJUNCTION
            .entrySet())
        {
            if (p.getValue() == null) {
                final Pair<PolyConstraintsSystem, PolyConstraintsSystem> pair = p.getKey();

                if ((a.getConstraints().containsAll(pair.x.getConstraints()) && b.getConstraints().containsAll(
                    pair.y.getConstraints()))
                    || (a.getConstraints().containsAll(pair.y.getConstraints()) && b.getConstraints().containsAll(
                        pair.x.getConstraints())))
                {
                    return PolyConstraintsSystem.FALSE;
                }
            }
        }

        final HashSet<SimplePolyConstraint> toRemove = new HashSet<>();

        for (final SimplePolyConstraint x : cons) {
            for (final SimplePolyConstraint y : cons) {

                if (x.equals(y) || toRemove.contains(y)) {
                    continue;
                }
                if (this.isInconsistant(x, y)) {
                    this.CONJUNCTION.put(pairA, PolyConstraintsSystem.FALSE);
                    return PolyConstraintsSystem.FALSE;
                }

                if (this.isImplied(x, y)) {
                    toRemove.add(y);
                    break;
                }
            }

        }

        cons.removeAll(toRemove);

        PolyConstraintsSystem c = PolyConstraintsSystem.create(cons);

        boolean requiresSat = !c.isLinear();

        if (!requiresSat) {
            final HashMap<String, HashSet<SimplePolyConstraint>> aUp = a.getLinearPart().getUpBoundedVars();
            final HashMap<String, HashSet<SimplePolyConstraint>> bLow = b.getLinearPart().getLowBoundedVars();

            for (final Entry<String, HashSet<SimplePolyConstraint>> varP : aUp.entrySet()) {
                final String var = varP.getKey();

                if (bLow.keySet().contains(var)) {
                    final HashSet<SimplePolyConstraint> constraints = new HashSet<>(varP.getValue());
                    constraints.retainAll(cons);

                    if (!b.getConstraints().containsAll(varP.getValue()) && !constraints.isEmpty()) {
                        requiresSat = true;
                        break;
                    }
                }
            }
        }

        if (!requiresSat) {
            final HashMap<String, HashSet<SimplePolyConstraint>> bUp = b.getLinearPart().getUpBoundedVars();
            final HashMap<String, HashSet<SimplePolyConstraint>> aLow = a.getLinearPart().getLowBoundedVars();

            for (final Entry<String, HashSet<SimplePolyConstraint>> varP : bUp.entrySet()) {
                final String var = varP.getKey();

                if (aLow.keySet().contains(var)) {
                    final HashSet<SimplePolyConstraint> constraints = new HashSet<>(varP.getValue());
                    constraints.retainAll(cons);

                    if (!a.getConstraints().containsAll(varP.getValue()) && !constraints.isEmpty()) {
                        requiresSat = true;
                        break;
                    }
                }
            }
        }

        if (requiresSat && this.isUNSAT(c)) {
            c = PolyConstraintsSystem.FALSE;
        }

        this.CONJUNCTION.put(pairA, c);

        return c;
    }

    private boolean isImplied(final SimplePolyConstraint a, final SimplePolyConstraint b) {
        for (final SimplePolyConstraint c : PolyConstraintsSystem.negate(b)) {
            if (!this.isInconsistant(a, c)) {
                return false;
            }
        }

        return true;
    }

    private boolean isInconsistant(final SimplePolyConstraint a, final SimplePolyConstraint b) {
        return false;
    }

    /**
     * @param a - constraints system
     * @param b - constraints system
     * @return fresh variables, functions, corresponding linear systems for a and b
     */
    @SuppressWarnings("unchecked")
    public
    Pair<Pair<HashMap<IndefinitePart, String>, HashMap<String, ArrayList<String>>>, Pair<LinearConstraintsSystem, LinearConstraintsSystem>>
    flatten(final PolyConstraintsSystem a, final PolyConstraintsSystem b)
    {
        final HashMap<SimplePolynomial, String> freshVars = new HashMap<>();
        final HashMap<String, ArrayList<String>> functions = new HashMap<>();
        final HashMap<IndefinitePart, String> originalIndefinite = new HashMap<>();

        this.flatten(a, freshVars, functions, originalIndefinite);
        this.flatten(b, freshVars, functions, originalIndefinite);

        final LinearConstraintsSystem linearA = this.toLinearConstraintsSystem(a, originalIndefinite);
        final LinearConstraintsSystem linearB = this.toLinearConstraintsSystem(b, originalIndefinite);

        return new Pair(new Pair(freshVars, functions), new Pair(linearA, linearB));
    }

    /**
     * @param indefiniteMap - indefinite parts map (renaming)
     * @return corresponding linear constraints system
     */
    public LinearConstraintsSystem toLinearConstraintsSystem(
        final PolyConstraintsSystem consSys,
        final HashMap<IndefinitePart, String> indefiniteMap)
    {
        final HashSet<SimplePolyConstraint> linearConstraints = new HashSet<>();

        for (final SimplePolyConstraint constraint : consSys.getConstraints()) {
            linearConstraints.add(ConstraintsSystemSolver.toLinearConstraint(constraint, indefiniteMap));
        }

        return new LinearConstraintsSystem(linearConstraints);
    }

    /**
     * @param constraint - constraint
     * @param indefiniteMap - indefinite parts map (renaming)
     * @return corresponding linear constraints system
     */
    private static SimplePolyConstraint toLinearConstraint(
        final SimplePolyConstraint constraint,
        final HashMap<IndefinitePart, String> indefiniteMap)
    {
        final ImmutableMap<IndefinitePart, BigInteger> map = constraint.getPolynomial().getSimpleMonomials();

        final ArrayList<SimplePolynomial> polyList = new ArrayList<>();

        for (final IndefinitePart indef : map.keySet()) {
            if (indefiniteMap.containsKey(indef)) {
                polyList
                .add(SimplePolynomial.create(IndefinitePart.create(indefiniteMap.get(indef), 1), map.get(indef)));
            } else if (indef.isLinear()) {
                polyList.add(SimplePolynomial.create(indef, map.get(indef)));
            } else {
                throw new RuntimeException();
            }
        }

        return new SimplePolyConstraint(SimplePolynomial.plus(polyList), constraint.getType());
    }

    /**
     * @param freshVars - fresh variables
     * @param functions - functions map
     * @param originalIndefinite - original indefinite parts
     */
    public void flatten(
        final PolyConstraintsSystem consSys,
        final HashMap<SimplePolynomial, String> freshVars,
        final HashMap<String, ArrayList<String>> functions,
        final HashMap<IndefinitePart, String> originalIndefinite)
    {

        for (final SimplePolyConstraint constraint : consSys.getConstraints()) {
            this.flatten(constraint.getPolynomial(), freshVars, functions, originalIndefinite);
        }
    }

    /**
     * @param poly - polynomial
     * @param freshVars - fresh variables
     * @param functions - functions map
     * @param originalIndefinite - original indefinite parts
     */
    private void flatten(
        final SimplePolynomial poly,
        final HashMap<SimplePolynomial, String> freshVars,
        final HashMap<String, ArrayList<String>> functions,
        final HashMap<IndefinitePart, String> originalIndefinite)
    {
        if (!poly.isLinear()) {
            for (final IndefinitePart indef : poly.getSimpleMonomials().keySet()) {

                final HashSet<String> varName = this.flatten(indef, freshVars, functions);

                final String name = varName == null ? null : varName.iterator().next();

                if (varName != null && !varName.equals(name)) {
                    originalIndefinite.put(indef, varName.iterator().next());
                }
            }
        }

    }

    /**
     * @param indef - indefinite part
     * @param freshVars - fresh variables
     * @param functions - functions map
     * @return set of corresponding new variables names
     */
    private HashSet<String> flatten(
        final IndefinitePart indef,
        final HashMap<SimplePolynomial, String> freshVars,
        final HashMap<String, ArrayList<String>> functions)
        {

        if (indef.isEmpty()) {
            return null;
        }

        final HashSet<String> result = new HashSet<>();

        final Map<String, Integer> expMap = indef.getExponents();

        for (final String varId : expMap.keySet()) {
            ConstraintsSystemSolver.flatten(varId, functions);
        }

        if (!result.isEmpty() && indef.isLinear()) {
            return result;
        }

        if (indef.isLinear()) {
            return null;
        }

        if (expMap.keySet().size() == 1) {

            final String a = expMap.keySet().iterator().next();

            if (expMap.get(a) == 2) {

                final SimplePolynomial poly = SimplePolynomial.create(IndefinitePart.create(expMap), BigInteger.ONE);
                final ArrayList<String> pair = new ArrayList<>();
                pair.add(a);
                pair.add(a);

                if (!functions.values().contains(pair)) {
                    final String id = this.getLastFreshVariableName(freshVars);

                    freshVars.put(poly, id);
                    functions.put(id, pair);

                    result.add(id);
                } else {
                    if (functions.values().contains(pair)) {
                        for (final String id : functions.keySet()) {
                            if (functions.get(id).equals(pair)) {
                                result.add(id);
                                break;
                            }
                        }

                    }
                }
                return result;
            }
        }

        if (expMap.keySet().size() == 2) {
            final ArrayList<String> vars = new ArrayList<>();

            for (final String var : expMap.keySet()) {
                vars.add(var);
            }

            final String a = vars.get(0);
            final String b = vars.get(1);

            if (expMap.get(a) == 1 && expMap.get(b) == 1) {

                final SimplePolynomial poly = SimplePolynomial.create(IndefinitePart.create(expMap), BigInteger.ONE);

                final ArrayList<String> pair1 = new ArrayList<>();
                final ArrayList<String> pair2 = new ArrayList<>();

                pair1.add(a);
                pair1.add(b);

                pair2.add(b);
                pair2.add(a);

                if (!functions.values().contains(pair1) && !functions.values().contains(pair2)) {
                    final String id = this.getLastFreshVariableName(freshVars);

                    freshVars.put(poly, id);
                    functions.put(id, pair1);

                    result.add(id);
                } else {
                    if (functions.values().contains(pair1)) {
                        for (final String id : functions.keySet()) {
                            if (functions.get(id).equals(pair1)) {
                                result.add(id);
                                break;
                            }
                        }

                    } else {
                        for (final String id : functions.keySet()) {
                            if (functions.get(id).equals(pair2)) {
                                result.add(id);
                                break;
                            }
                        }
                    }
                }
                return result;
            }
        }

        for (final String var : expMap.keySet()) {
            final Map<String, Integer> expMapNew = new HashMap<>();

            for (final String v : expMap.keySet()) {
                final int n = expMap.get(v);

                if (v.equals(var)) {
                    if (n > 1) {
                        expMapNew.put(v, n - 1);
                    }
                } else {
                    expMapNew.put(v, n);
                }
            }

            final HashSet<String> partIndef = this.flatten(IndefinitePart.create(expMapNew), freshVars, functions);

            for (final String p : partIndef) {
                final Map<String, Integer> expMapComp = new HashMap<>();

                expMapComp.put(var, 1);
                expMapComp.put(p, 1);

                final SimplePolynomial poly = SimplePolynomial.create(IndefinitePart.create(expMap), BigInteger.ONE);

                final String id = this.getLastFreshVariableName(freshVars);

                result.add(id);

                freshVars.put(poly, id);

                final ArrayList<String> pair = new ArrayList<>();
                pair.add(var);
                pair.add(p);

                functions.put(id, pair);
            }
        }

        return result;
        }

    private static void flatten(final String varId, final HashMap<String, ArrayList<String>> functions) {

        if (!functions.containsKey(varId) && VariableNode.isArrayEntry(varId)) {
            final String indVar = VariableNode.getArrayIndex(varId);

            final ArrayList<String> item = new ArrayList<>();

            item.add(indVar);

            functions.put(varId, item);
        }
    }

    private String createFreshVariableName(final HashMap<SimplePolynomial, String> freshVars) {
        return "v_" + freshVars.size();
    }

    private String getLastFreshVariableName(final HashMap<SimplePolynomial, String> freshVars) {
        return "v_" + (freshVars.size() - 1);
    }

    public boolean implies(final PolyConstraintsSystem a, final PolyConstraintsSystem b) {
        return this.checkImplication(a, b);
    }

    private final Map<SimplePolynomial, ImmutableMap<String, ArrayList<String>>> POLYNOMIAL_ARRAY = new HashMap<>();

    private final Map<Pair<PolyConstraintsSystem, ImmutableSet<String>>, PolyConstraintsSystem> RESTRICTED =
        new HashMap<>();

        private final Map<PolyConstraintsSystem, ImmutableMap<String, BigInteger>> SOLUTIONS = new HashMap<>();
        private final Map<PolyConstraintsSystem, YNM> SAT = new HashMap<>();

        private final Map<PolyConstraintsSystem, ImmutableSet<String>> VARIABLES = new HashMap<>();

        /**
         * Maps each pair of constraints systems to their conjunction system
         */
        private final Map<Pair<PolyConstraintsSystem, PolyConstraintsSystem>, PolyConstraintsSystem> CONJUNCTION =
            new HashMap<>();

    private static Map<Pair<PolyConstraintsSystem, PolyConstraintsSystem>, Boolean> IMPLIES_MAP = new HashMap<>();
}
