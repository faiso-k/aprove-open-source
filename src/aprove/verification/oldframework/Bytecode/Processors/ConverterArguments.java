package aprove.verification.oldframework.Bytecode.Processors;

public class ConverterArguments {
    /**
     * Switch controlling if we only encode interesting references. Should be true in every reasonable environment.
     */
    public boolean encodeOnlyInterestingRefs = true;

    /**
     * Encode static field values into the states.
     */
    public boolean encodeStaticFields = true;

    /**
     * Encode the path length of all occurring instances next to the
     * term.
     */
    public boolean encodePathLength = false;

    /**
     * Put in a term encoding of reference type values in the state terms.
     */
    public boolean encodeReferenceTypesAsTerms = true;

    /**
     * Encode the length of arrays in separately.
     */
    public boolean encodeArrayLengthSeparately = false;

    /**
     * Use a "flat" term encoding, where new function symbols for stackframes
     * are only introduced when splitting happens in the method graph.
     */
    public boolean useFlatEncoding = true;

    /**
     * Encode the distances indicated by definite reachability annotations?
     */
    public boolean encodeReferenceDistances = true;
}
