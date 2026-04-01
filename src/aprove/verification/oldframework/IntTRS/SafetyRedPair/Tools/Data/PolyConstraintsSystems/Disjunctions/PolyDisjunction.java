package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import immutables.*;

/**
 * Disjunction of polynomial constraints systems
 * @author marinag
 *
 */
public class PolyDisjunction {

    /**
     * Constraints systems set
     */
    protected final ImmutableSet<PolyConstraintsSystem> constraintsSystems;

    public static PolyDisjunction TRUE = PolyDisjunction.create(true);
    public static PolyDisjunction FALSE = PolyDisjunction.create(false);

    protected PolyDisjunction(final Collection<PolyConstraintsSystem> constraints) {
        HashSet<PolyConstraintsSystem> c = new HashSet<>();

        for ( final PolyConstraintsSystem constraint : constraints) {
            if (!constraint.isFalse()) {
                if (constraint.isTrue()) {
                    c = ImmutableCreator.create(new HashSet<PolyConstraintsSystem>(Arrays.asList(constraint)));
                    break;
                } else {
                    c.add(constraint);
                }
            }
        }

        this.constraintsSystems = ImmutableCreator.create(c);
    }


    public static PolyDisjunction create(final SimplePolyConstraint constraint) {
        return PolyDisjunction.create(PolyConstraintsSystem.create(constraint));
    }


    public static PolyDisjunction create(final Collection<PolyConstraintsSystem> constraints) {

        return new PolyDisjunction(constraints);
    }

    public static PolyDisjunction create(final boolean value) {
        final HashSet<PolyConstraintsSystem> constraints = new HashSet<>();

        if (value) {
            constraints.add(PolyConstraintsSystem.TRUE);
        }

        return PolyDisjunction.create(constraints);
    }

    public static PolyDisjunction create(final PolyConstraintsSystem... constraints) {
        return PolyDisjunction.create(Arrays.asList(constraints));
    }

    public static PolyDisjunction merge(final PolyDisjunction a, final PolyDisjunction b) {
        PolyDisjunction result = a;

        for (final PolyConstraintsSystem c : b.getConstraintsSystems()) {
            result = result.addSystem(c);
        }

        return result;
    }


    public PolyDisjunction rename(final Map<String, String> revMap) {
        PolyDisjunction result = PolyDisjunction.FALSE;

        for (final PolyConstraintsSystem consSys : this.getConstraintsSystems()) {
            result = result.addSystem(consSys.rename(revMap));
        }

        return result;
    }

    public PolyDisjunction mergeSystem(final PolyConstraintsSystem restSys) {
        final Set<PolyConstraintsSystem> sys = this.getConstraintsSystems();
        sys.add(restSys);
        return PolyDisjunction.create(sys);
    }


    @Override
    public Object clone() {
        return new PolyDisjunction(this.getConstraintsSystems());
    }

    /**
     * Add constraintsSys
     * @param constraintsSys - constraints system
     */
    public PolyDisjunction addSystem(final PolyConstraintsSystem constraintsSys) {
        if (this.isTrue() && constraintsSys.isEmpty()) {
            return this;
        }

        PolyConstraintsSystem toRemove = null;
        for (final PolyConstraintsSystem c : this.getConstraintsSystems()) {
            if (c.equals(constraintsSys) || constraintsSys.getConstraints().containsAll(c.getConstraints())) {
                return this;
            }
            if (c.getConstraints().containsAll(constraintsSys.getConstraints())) {
                toRemove = c;
                break;
            }
        }

        final Set<PolyConstraintsSystem> cons = this.getConstraintsSystems();

        if (toRemove != null) {
            cons.remove(toRemove);
        }

        cons.add(constraintsSys);

        return new PolyDisjunction(cons);
    }

    /**
     * @param systems polynomial constraints systems
     * @return this disjunction with all the systems added
     */
    public PolyDisjunction addAllSystems(final Collection<PolyConstraintsSystem> systems) {

        PolyDisjunction result = this;

        for (final PolyConstraintsSystem c : systems) {
            result = result.addSystem(c);
        }

        return result;
    }

    /**
     * @param disjunctions - collection of disjunctions
     * @return merge of this with disjunctions (this is not affected)
     */
    public PolyDisjunction mergeAll(final Collection<PolyDisjunction> disjunctions) {
        PolyDisjunction disj = this;

        for (final PolyDisjunction d : disjunctions) {
            disj = disj.mergeAll(d);
        }
        return disj;
    }

    /**
     * @param disjunction polynomial disjunction
     * @return true if this disjunction contains all the systems of the given disjunction
     */
    public boolean contains(final PolyDisjunction disjunction) {
        return this.constraintsSystems.containsAll(disjunction.constraintsSystems);
    }

    /**
     * @ disjunction - PolyDisjunction
     * @return merge of this with given disjunction parameter
     */
    public PolyDisjunction mergeAll(final PolyDisjunction disjunction) {
        if (disjunction.isEmpty()) {
            return this;
        }
        if (this.isEmpty()) {
            return disjunction;
        }

        PolyDisjunction c = PolyDisjunction.FALSE;

        for (final PolyConstraintsSystem a : disjunction.getConstraintsSystems()) {
            for (final PolyConstraintsSystem b : this.getConstraintsSystems()) {
                @SuppressWarnings("unchecked")
                final
                PolyConstraintsSystem cons = PolyConstraintsSystem.merge(a, b);
                c = c.addSystem(cons);
            }
        }

        return c;
    }

    /**
     * @param constraintsSys -constraints systems
     * @return this after removal of all constraints from constraintsSys
     */
    public PolyDisjunction remove(final PolyConstraintsSystem constraintsSys) {
        final Set<PolyConstraintsSystem> consSys = new HashSet<>();

        for (final PolyConstraintsSystem c : this.getConstraintsSystems()) {
            consSys.add(c.remove(constraintsSys.getConstraints()));
        }

        return PolyDisjunction.create(consSys);
    }

    /**
     * @ disjunction - PolyDisjunction of constraints systems
     * @return this after removal of PolyDisjunction
     */
    public PolyDisjunction remove(final  PolyDisjunction disjunction) {
        for (final PolyConstraintsSystem c : disjunction.getConstraintsSystems()) {
            this.remove(c);
        }

        final HashSet<PolyConstraintsSystem> toRemove = new HashSet<>();

        for (final PolyConstraintsSystem a : disjunction.getConstraintsSystems()) {
            if (toRemove.contains(a)) {
                continue;
            }
            for (final PolyConstraintsSystem b : disjunction.getConstraintsSystems()) {
                if (a == b || toRemove.contains(b)) {
                    continue;
                }

                if (a.getConstraints().contains(b.getConstraints())) {
                    toRemove.add(b);
                }
            }
        }

        final Set<PolyConstraintsSystem> constraints = this.getConstraintsSystems();

        constraints.removeAll(toRemove);

        return PolyDisjunction.create(constraints);
    }

    /**
     * @return true if represents true (no constraints), false otherwise
     */
    public boolean isTrue() {
        for (final PolyConstraintsSystem sys : this.getConstraintsSystems()) {
            if (sys.isEmpty()) {
                return true;
            }
        }
        return false;
    }


    /**
     * @return Constraint systems set
     */
    public Set<PolyConstraintsSystem> getConstraintsSystems() {
        return new HashSet<>(this.constraintsSystems);
    }

    /**
     * @return true if contains no constraints, false otherwise
     */
    public boolean isEmpty() {
        if (this.constraintsSystems.contains(PolyConstraintsSystem.FALSE) && this.constraintsSystems.size() == 1) {
            return true;
        }

        return this.getConstraintsSystems().isEmpty();

    }



    @Override
    public String toString() {
        if (this.isEmpty()) {
            return "Empty";
        }

        return this.constraintsSystems.toString();
    }

    private Set toSet() {
        return new HashSet<>(this.getConstraintsSystems());
    }

    @Override
    public boolean equals(final Object disj) {
        if (disj == null || !(disj instanceof PolyDisjunction)) {
            return false;
        }

        if (this == disj) {
            return true;
        }

        final PolyDisjunction d = (PolyDisjunction) disj;

        if ((d.isEmpty() && this.isEmpty()) || (d.isTrue() && this.isTrue())) {
            return true;
        }

        return this.getConstraintsSystems().equals(d.getConstraintsSystems());
    }

    @Override
    public int hashCode() {
        return this.toSet().hashCode();
    }


    /**
     * @param valueMap map of assigment value to each variable name
     * @return resulting value or null if evaluation was not possible (due to missing variables values)
     */
    public Boolean tryEvaluate(final Map<String, BigInteger> valueMap) {
        boolean requireTrue = false;

        for (final PolyConstraintsSystem c : this.constraintsSystems) {
            final Boolean value = c.tryEvaluate(valueMap);

            if (value == null) {
                requireTrue = true;
            } else {
                if (value) {
                    return true;
                }
            }
        }
        return requireTrue ? null : false;
    }

    /**
     * @param consSys polynomial constraints system
     * @return disjunction without the given system
     */
    public PolyDisjunction removeConstraintsSystem(final PolyConstraintsSystem consSys) {
        final Set<PolyConstraintsSystem> s = this.toSet();
        s.remove(consSys);
        return PolyDisjunction.create(s);
    }

    public PolyDisjunction restrictVariables(final Set<String> variables) {
        final Set<PolyConstraintsSystem> constraintsSys = new HashSet<>();

        for (final PolyConstraintsSystem c : this.constraintsSystems) {
            constraintsSys.add(c.restrictVariables(variables));
        }

        return PolyDisjunction.create(constraintsSys);

    }

    public TRSTerm toTerm() {
        if (this.isTrue()) {
            return ToolBox.buildTrue();
        }
        if (this.isEmpty()) {
            return ToolBox.buildFalse();
        }

        final Set<TRSTerm> terms = new HashSet<>();

        TRSTerm result = null;
        for (final PolyConstraintsSystem cons : this.getConstraintsSystems()) {
            result = result == null ? cons.toTerm() : ToolBox.buildOr(cons.toTerm(), result);
        }

        return result;
    }

    public PolyDisjunction disjunction(final PolyDisjunction disj) {
        if (this.isTrue() || disj.isTrue()) {
            return PolyDisjunction.TRUE;
        }

        final Set<PolyConstraintsSystem> consSys = this.getConstraintsSystems();
        consSys.addAll(disj.getConstraintsSystems());

        return PolyDisjunction.create(consSys);
    }

    public PolyDisjunction negate() {
        if (this.isTrue()) {
            return PolyDisjunction.FALSE;
        }

        if (this.isEmpty()) {
            return PolyDisjunction.TRUE;
        }

        PolyDisjunction result = PolyDisjunction.TRUE;

        for (final PolyConstraintsSystem c : this.getConstraintsSystems()) {
            result = result.mergeAll(c.negate());
        }

        return result;
    }

    public Set<String> getVariables() {
        final HashSet<String> vars = new HashSet<>();

        for (final PolyConstraintsSystem c : this.getConstraintsSystems()) {
            vars.addAll(c.getVariables());

        }

        return vars;
    }

}
