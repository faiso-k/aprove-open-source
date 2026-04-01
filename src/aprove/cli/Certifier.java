package aprove.cli;


/**
 * Defines certifiers and their capabilities.
 *
 * @author CKuknat
 */

public enum Certifier {
    NONE(new String[0],
            null,
            false, false, false, false),
    RAINBOW(new String[] { "color", "rainbow" },
            "aprove.Certify.color-nograph",
            true, false, false, true),
    A3PAT(new String[] { "a3pat", "cime", "coccinelle" },
            "aprove.Certify.a3pat-nograph",
            false, true, false, true),
    CETA(new String[] { "ceta", "isafor" },
            "aprove.Auto.current",
            false, false, true, true);

    private final String [] certifier;
    private final String defaultStrategyName;
    private final boolean rainbow, a3pat, ceta;
    private final boolean cpf;

    /**
     * @param certifier - names by which this Certifier is recognized (ignoring case)
     * @param defaultStrategyName - the name of the internal default strategy for
     *  this Certifier
     */
    private Certifier(String [] certifier, String defaultStrategyName,
            boolean rainbow, boolean a3pat, boolean ceta, boolean cpf) {
        this.certifier = certifier;
        this.defaultStrategyName = defaultStrategyName;
        this.rainbow = rainbow;
        this.a3pat = a3pat;
        this.ceta = ceta;
        this.cpf = cpf;
    }

    public boolean isRainbow() {
        return this.rainbow;
    }

    public boolean isA3pat() {
        return this.a3pat;
    }

    public boolean isCeta() {
        return this.ceta;
    }

    public boolean isCpf() {
        return this.cpf;
    }

    public boolean isNone() {
        return !(this.a3pat || this.ceta || this.cpf || this.rainbow);
    }

    /**
     * @return the name of the (internal) strategy used by default for
     *  this certifier
     */
    public final String getDefaultStrategyName() {
        return this.defaultStrategyName;
    }

    public static Certifier parseName(String certifier){
        for (Certifier cert : Certifier.values()) {
            for (String value : cert.certifier) {
                if (value.equalsIgnoreCase(certifier)) {
                        return cert;
                }
            }
        }
        return null;
    }
}
