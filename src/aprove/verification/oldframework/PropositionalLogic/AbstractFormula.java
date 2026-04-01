package aprove.verification.oldframework.PropositionalLogic;

public abstract class AbstractFormula<T> implements Formula<T> {

    /**
     *
     */
    private static final long serialVersionUID = -3533817800914370056L;

    // "magic number" to indicate that the formula id (which will correspond
    // to the number of a literal in the Dimacs format CNF) has not been set.
    // Since positive integers denote variables and negative integers denote
    // negated variables, 0 is a sane value here. (And comparison with
    // zero should be efficient :) )
    public static final int ID_UNSET = 0;

    // The number that will represent this particular (sub)formula in
    // the (Extended) Dimacs format representation of the overall formula;
    // initially unset.
    protected int id = AbstractFormula.ID_UNSET;

    /**
     * label *this node only* without generating gates.
     * @param id The id to label this node with. Can be negative.
     */
    @Override
    public void labelThisWith(int id) {
        this.id = id;
    }


    protected CircuitGate gate = null; // will store the gate representation of this

    public void clearGate() {
        this.gate = null;
    }

    /**
     * Default implementation: false
     *
     * @return whether this is a TheoryAtom (false for most formulae,
     *  hence false by default)
     */
    @Override
    public boolean isTheoryAtom() {
        return false;
    }
}
