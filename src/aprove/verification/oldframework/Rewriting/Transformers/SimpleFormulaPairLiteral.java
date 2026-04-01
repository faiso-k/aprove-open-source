package aprove.verification.oldframework.Rewriting.Transformers;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Class that encapsulates a literal for a SimpleFormula
 *  and provides equals() and hashCode() functions
 *
 * @author matraf
 */
public class SimpleFormulaPairLiteral<T1, T2> extends Pair<T1, T2> {

    private SimpleFormulaPairLiteral(final T1 x, final T2 y) {
        super(x, y);
    }

    public static <T1, T2> SimpleFormulaPairLiteral<T1, T2> createLiteral(final T1 x, final T2 y) {
        return new SimpleFormulaPairLiteral<T1, T2>(x, y);
    }

    @Override
    public boolean equals(final Object o) {
        if (!(o instanceof SimpleFormulaPairLiteral)) {
            return false;
        }

        final SimpleFormulaPairLiteral that = (SimpleFormulaPairLiteral) o;
        return this.x.equals(that.x) && this.y.equals(that.y);
    }

    @Override
    public int hashCode() {
        return this.x.hashCode() + this.y.hashCode();
    }

    @Override
    public String toString() {
        return "(" + this.x.toString() + "," + this.y.toString() + ")";
    }

}
