package aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 * Exotic algebrae are semirings using plus for multiplication
 * and max or min for addition.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class ExoticAlgebra<T extends ExoticInt<T>> extends Semiring.SemiringSkeleton<T> {

    /**
     * Addition operation.
     */
    @Override
    public T plus(T first, T second) {
        return first.plus(second);
    }

    /**
     * Multiplication operation.
     */
    @Override
    public T times(T first, T second) {
        return first.times(second);
    }

    /**
     * The neutral element of multiplication.
     */
    @Override
    abstract public T one();

    /**
     * The neutral element of addition, and zero element
     * of multiplication.
     */
    @Override
    abstract public T zero();

    @Override
    public SpecializedGInterpretation getSpecializedGInterpretation() {
        return DummySpecializedGInterpretation.create();
    }

}