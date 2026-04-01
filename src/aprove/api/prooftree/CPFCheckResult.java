package aprove.api.prooftree;

/**
 * Indicates how the certification was finished.
 */
public enum CPFCheckResult {
                            Certified,
                            UnsupportedByCertifier,
                            RejectedByCertifier,
                            TimeoutByCertifier,
                            ErrorInvokingCertifier,
                            ErrorWhenGeneratingCPF,
                            CeTAnotAvailable,
                            NoBasicObligation;
}
