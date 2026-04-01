package aprove.api.prooftree.impl;

import aprove.api.prooftree.*;

public class CertificationResultImpl implements CertificationResult {

    private final CPFCheckResult checkResult;
    private final int numberOfRealProofs;
    private final int numberOfAssumptions;
    private final int numberOfUnknownProofs;

    public CertificationResultImpl(CPFCheckResult checkResult,
                                   int numberOfRealProofs,
                                   int numberOfAssumptions,
                                   int numberOfUnknownProofs) {
        this.checkResult = checkResult;
        this.numberOfRealProofs = numberOfRealProofs;
        this.numberOfAssumptions = numberOfAssumptions;
        this.numberOfUnknownProofs = numberOfUnknownProofs;
    }

    @Override
    public CPFCheckResult getCheckResult() {
        return checkResult;
    }

    @Override
    public int getNumberOfRealProofs() {
        return numberOfRealProofs;
    }

    @Override
    public int getNumberOfAssumptions() {
        return numberOfAssumptions;
    }

    @Override
    public int getNumberOfUnknownProofs() {
        return numberOfUnknownProofs;
    }
}
