package aprove.xml;

public interface CPFModus {
    /**
     * should we generate a proof, or a disproof
     */
    public boolean isPositive();

    /**
     * points to the critical subproof which leads to
     * the overall subproof, counting starts from 0
     */
    public int negativeReason();
}
