package aprove.verification.oldframework.IRSwT.Engines.Formulae;

/**
 * Represents formulae of arity two.
 * @author Matthias Hoelzel
 * @param <A> type of atoms
 */
public abstract class TwoAryFormula<A extends CheckableAndSMTExportable> extends AbstractFormula<A> {
    /** The left formula */
    protected AbstractFormula<A> left;

    /** The right formula */
    protected AbstractFormula<A> right;

    /**
     * Constructor!
     * @param leftFormula the left formula
     * @param rightFormula the right formula
     */
    public TwoAryFormula(final AbstractFormula<A> leftFormula, final AbstractFormula<A> rightFormula) {
        this.left = leftFormula;
        this.right = rightFormula;
    }
}
