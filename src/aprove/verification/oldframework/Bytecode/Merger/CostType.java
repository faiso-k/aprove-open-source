package aprove.verification.oldframework.Bytecode.Merger;


/**
 * Enumeration of possible reasons to add costs when merging, including the costs associated with each of these reasons.
 *
 * @author Marc Brockschmidt
 */
public enum CostType {
    /**
     * No actual cost (needed for technical reasons).
     */
    NONE(0.),

    /**
     * The cost for widening an integer to a finite interval. Is multiplied with 1/n, where n is the length of the
     * minimal position for the changed reference.
     */
    INTERVAL_FINITE(1.0),

    /**
     * The cost for widening an integer to an infinite interval. Is multiplied with 1/n, where n is the length of the
     * minimal position for the changed reference.
     */
    INTERVAL_INFINITE(3.0),

    /**
     * Some cost for losing information about floats. Is multiplied with 1/n, where n is the length of the minimal
     * position for the changed reference.
     */
    FLOAT(1),

    /**
     * The cost for forgetting about an object's existence.
     */
    LOST_EXISTENCE(3.0),

    LOST_SIMPLE_EXISTENCE(100.0),

    /**
     * The cost for forgetting about an object's nonexistence.
     */
    LOST_NONEXISTENCE(3.5),

    /**
     * The cost for introducing possible equality of two different variable references.
     */
    LOST_INEQUALITY(5.0),

    /**
     * This cost is introduced every time we add x =?= y where in the original state the corresponding references were
     * the same.
     */
    LOST_EQUALITY(5.0),

    /**
     * The cost for introducing a "non-tree annotation" for a variable reference that was not allowed to have a non-tree
     * shape before.
     */
   LOST_TREE(15.0),

    /**
     * The cost for introducing a "possibly cyclic" annotation for a variable reference that was not allowed to be
     * cyclic before.
     */
    LOST_CYCLE_INFORMATION(25.0),

    /**
     * The cost for introducing a "possibly joining" annotation for of two variable references.
     */
    POSSIBLY_JOINING(10.0),

    /**
     * The cost for forgetting type information.
     */
    LOST_TYPEINFO(2.0),

    /**
     * The cost for forgetting information about one slice of a realized type.
     */
    LOST_REALIZED_INFO(2.0),

    /**
     * The cost for adding a new input reference.
     */
    ADDED_INPUTREF(1.0),

    /**
     * The cost for modifying the changed-bit of an input reference.
     */
    MODIFIED_INPUTREF(1.0),

    /**
     * The cost for losing a definite reaches annotation.
     */
    LOST_DEFREACH(10.0),

    /**
     * The cost for losing a cycle joint.
     */
    LOST_CYCLEJOINT(Double.POSITIVE_INFINITY),

    /**
     * The cost for losing array information (a[i] = c).
     */
    LOST_ARRAYINFO(1.0),

    /** we lost an integer relation */
    LOST_INT_REL(0.5),

    LOST_CONCRETE_STRING(0.5),

    LOST_CLASS_INSTANCE(0.25);

    /**
     * The actual cost associated with a certain cost type.
     */
    private final double costValue;

    /**
     * @param costVal actual cost associated with a certain cost type.
     */
    private CostType(final double costVal) {
        this.costValue = costVal;
    }

    public double getCostValue() {
        return this.costValue;
    }
}
