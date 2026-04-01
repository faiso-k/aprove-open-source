package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch;

/**
 * Interface for factories for arithmetic circuits that may use
 * only a bounded number of bits.
 *
 * @author Carsten Fuhs
 */
public interface BoundedCircuitFactory {

    /**
     * @return the overflows that have been accumulated during circuit
     * construction since the last reset
     */
    abstract public Overflows getOverflows();

    /**
     * Resets the formula that constrains the arithmetic circuit not to exceed
     * its allowed maximum value (e.g., because we want to process another
     * atomic constraint now).
     */
    abstract public void reset();
}
