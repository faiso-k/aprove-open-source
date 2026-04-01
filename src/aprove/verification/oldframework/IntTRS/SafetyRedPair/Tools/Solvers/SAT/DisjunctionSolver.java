package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Disjunction of Polynomial constraints system solver
 * @author marinag
 */
public class DisjunctionSolver {
    private final ConstraintsSystemSolver solver;
    private final Abortion aborter;

    private DisjunctionSolver(final ConstraintsSystemSolver solver, final Abortion aborter) {
        this.aborter = aborter;
        this.solver = solver;
    }

    public static DisjunctionSolver create(final ConstraintsSystemSolver solver, final Abortion aborter) {
        return new DisjunctionSolver(solver, aborter);
    }

    public PolyDisjunction negate(final PolyDisjunction disjunction) {

        if (disjunction.isEmpty()) {
            return PolyDisjunction.TRUE;
        }

        if (disjunction.isTrue()) {
            return PolyDisjunction.FALSE;
        }

        PolyDisjunction result = PolyDisjunction.TRUE;

        for (final PolyConstraintsSystem c : disjunction.getConstraintsSystems()) {
            result = this.conjunction(result, c.negate());
        }

        return result;
    }

    public PolyDisjunction restrict(final PolyDisjunction disjunction, final Set<String> variables) {
        PolyDisjunction result = PolyDisjunction.FALSE;

        HashSet<String> vars = new HashSet(variables);
        final HashSet<String> tvars = new HashSet<>();

        while (!vars.isEmpty() && !result.getConstraintsSystems().containsAll(disjunction.getConstraintsSystems())) {
            tvars.addAll(vars);

            vars = new HashSet<>();

            for (final PolyConstraintsSystem consSys : disjunction.getConstraintsSystems()) {
                if (result.getConstraintsSystems().contains(consSys)) {
                    continue;
                }

                final PolyConstraintsSystem restSys = this.solver.restrictVariables(consSys, tvars);

                if (!restSys.isEmpty()) {
                    result = result.mergeSystem(restSys);

                    vars.addAll(restSys.getVariables());
                }
            }

            vars.removeAll(tvars);
        }

        final HashSet<PolyConstraintsSystem> toRemove = new HashSet<>();

        for (final PolyConstraintsSystem a : result.getConstraintsSystems()) {
            for (final PolyConstraintsSystem b : result.getConstraintsSystems()) {
                if (a.equals(b)) {
                    continue;
                }

                if (a.getConstraints().containsAll(b.getConstraints())) {
                    toRemove.add(b);
                }
            }
        }

        result.getConstraintsSystems().removeAll(toRemove);

        return result;
    }

    /**
    //   * @param disjunctions - collection of disjunctions
    //   * @return conjunction of this with disjunctions (this is not affected)
    //   */
    public
    PolyDisjunction
    conjunction(final PolyDisjunction disjunction, final Collection<PolyDisjunction> disjunctions)
    {
        PolyDisjunction disj = disjunction;

        for (final PolyDisjunction d : disjunctions) {
            if (disj.isEmpty()) {
                return disj;
            }

            disj = this.conjunction(disj, d);
        }
        return disj;
    }

    public LinearDisjunction conjunction(
        final LinearDisjunction disjunctionA, final LinearDisjunction disjunctionB)
    {
        return LinearDisjunction.create(this.conjunction(
            PolyDisjunction.create(disjunctionA.getConstraintsSystems()),
            PolyDisjunction.create(disjunctionB.getConstraintsSystems())));
    }

    public PolyDisjunction conjunction(
        final PolyDisjunction disjunctionA,
        final PolyDisjunction disjunctionB)
    {
        if (disjunctionA.isEmpty() || disjunctionB.isEmpty()) {
            return PolyDisjunction.FALSE;
        }

        if (disjunctionA.equals(disjunctionB) || disjunctionB.isTrue()) {
            return disjunctionA;
        }
        if (disjunctionA.isTrue()) {
            return disjunctionB;
        }

        final Pair<Object, Object> pairA = new Pair<Object, Object>(disjunctionA, disjunctionB);
        final Pair<Object, Object> pairB = new Pair<Object, Object>(disjunctionB, disjunctionA);

        if (this.CONJUNCTION.containsKey(pairA)) {
            return this.CONJUNCTION.get(pairA);
        }

        if (this.CONJUNCTION.containsKey(pairB)) {
            return this.CONJUNCTION.get(pairB);
        }

        PolyDisjunction result = PolyDisjunction.FALSE;

        for (final PolyConstraintsSystem a : disjunctionA.getConstraintsSystems()) {
            for (final PolyConstraintsSystem b : disjunctionB.getConstraintsSystems()) {
                final PolyConstraintsSystem c = this.solver.conjunction(a, b);

                if (!c.isFalse() && !result.getConstraintsSystems().contains(c)) {
                    result = result.addSystem(c);
                }

            }

        }

        this.CONJUNCTION.put(pairA, result);

        return result;
    }

    /**
     * @return Set of all variables names
     */
    synchronized public Set<String> getVariables(final PolyDisjunction disjunction) {
        if (this.VARIABLES.containsKey(disjunction)) {
            return this.VARIABLES.get(disjunction);
        }

        final HashSet<String> vars = new HashSet<>();

        for (final PolyConstraintsSystem c : disjunction.getConstraintsSystems()) {
            vars.addAll(c.getVariables());

        }
        this.VARIABLES.put(disjunction, ImmutableCreator.create(vars));

        return vars;
    }

    public boolean isSAT(final PolyDisjunction disjunction) {
        for (final PolyConstraintsSystem c : disjunction.getConstraintsSystems()) {
            if (this.solver.isSAT(c)) {
                return true;
            }
        }
        return false;
    }


    public boolean isConsistantWith(
        final PolyDisjunction disjunction,
        final Collection<PolyDisjunction> disjunctions)
    {
        return !this.conjunction(disjunction, disjunctions).isEmpty();
    }

    public boolean isConsistantWith(
        final PolyDisjunction disjunction,
        final PolyDisjunction disj)
    {
        final HashSet<PolyDisjunction> set = new HashSet<>();
        set.add(disj);
        return this.isConsistantWith(disjunction, set);
    }

    public boolean isUNSAT(final PolyDisjunction disj) {
        for (final PolyConstraintsSystem c : disj.getConstraintsSystems()) {
            if (!this.solver.isUNSAT(c)) {
                return false;
            }
        }

        return true;
    }

    public static HashMap<PolyConstraintsSystem, PolyDisjunction> NEGATION = new HashMap<>();

    private final Map<PolyDisjunction, PolyDisjunction> NEGATION_DISJ = new HashMap<>();

    private final Map<PolyDisjunction, ImmutableSet<ImmutableMap<IndefinitePart, BigInteger>>> SOLUTIONS =
        new HashMap<>();

        private final Map<Pair<Object, Object>, PolyDisjunction> CONJUNCTION = new HashMap<>();

        private final Map<Pair<PolyDisjunction, PolyDisjunction>, Boolean> CONSISTANT = new HashMap<>();

        private final Map<PolyConstraintsSystem, ImmutableMap<IndefinitePart, BigInteger>> SYSTEMS_SOLUTIONS =
            new HashMap<>();
            private final Map<PolyConstraintsSystem, Boolean> SYSTEMS_SAT = new HashMap<>();

            private final Map<PolyDisjunction, HashSet<String>> VARIABLES = new HashMap<>();


}
