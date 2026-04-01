package aprove.api.prooftree;

/**
 * Contains the result of a certification.
 */
public interface CertificationResult {

    CPFCheckResult getCheckResult();

    int getNumberOfRealProofs();

    int getNumberOfAssumptions();

    int getNumberOfUnknownProofs();
}
