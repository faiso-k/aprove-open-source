package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions;

import java.util.*;

import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;

/**
 * Disjunction of linear constraints systems
 * @author marinag
 *
 */
public class LinearDisjunction extends PolyDisjunction {

    /**
     * True
     */
    public static LinearDisjunction TRUE = LinearDisjunction.create(true);
    /**
     * False
     */
    public static LinearDisjunction FALSE = LinearDisjunction.create(false);


    protected LinearDisjunction(final Collection<PolyConstraintsSystem> constraints) {
        super(constraints);
    }

    public static LinearDisjunction create(final boolean value) {
        final HashSet<PolyConstraintsSystem> constraints = new HashSet<>();

        if (value) {
            constraints.add(PolyConstraintsSystem.TRUE);
        }

        return LinearDisjunction.create(constraints);
    }

    public static LinearDisjunction create(final Collection<PolyConstraintsSystem> constraints) {
        final HashSet<PolyConstraintsSystem> polyCons = new HashSet<>();

        for (final PolyConstraintsSystem c : constraints) {
            polyCons.add(LinearConstraintsSystem.create(c));
        }

        return new LinearDisjunction(polyCons);
    }

    public static LinearDisjunction create(final LinearConstraintsSystem constraint) {
        final HashSet<PolyConstraintsSystem> constraints = new HashSet<>();

        constraints.add(constraint);

        return LinearDisjunction.create(constraints);
    }

    public Set<LinearConstraintsSystem> getLinearConstraintsSystems() {
        final HashSet<LinearConstraintsSystem> polyCons = new HashSet<>();

        for (final PolyConstraintsSystem c : this.constraintsSystems) {
            polyCons.add(LinearConstraintsSystem.create(c));
        }

        return polyCons;
    }

    public static LinearDisjunction create(final PolyDisjunction disjunction) {
        return LinearDisjunction.create(disjunction.constraintsSystems);
    }


    public static LinearDisjunction merge(final PolyDisjunction a, final PolyDisjunction b) {
        return LinearDisjunction.create(PolyDisjunction.merge(a, b));
    }

    @Override
    public LinearDisjunction addSystem(final PolyConstraintsSystem sys) {
        return LinearDisjunction.create(super.addSystem(sys));
    }

    @Override
    public LinearDisjunction negate() {
        return LinearDisjunction.create(super.negate());
    }

    public static LinearDisjunction create(final Set<LinearConstraintsSystem> constraints) {
        final Set<PolyConstraintsSystem> polyCon = new HashSet<>();

        for (final LinearConstraintsSystem c : constraints) {
            polyCon.add(c);
        }

        return LinearDisjunction.create(polyCon);
    }

    public LinearDisjunction addToAll(final LinearConstraintsSystem linSys) {
        final Set<PolyConstraintsSystem> polyCon = new HashSet<>();

        for (final PolyConstraintsSystem c : this.constraintsSystems) {
            polyCon.add(c.merge(linSys));
        }

        return LinearDisjunction.create(polyCon);
    }

}
