package aprove.verification.dpframework.Utility.NonLoop.structures;

import aprove.prooftree.Export.Utility.*;

/**
 * This interfaces provides two methods for proof export.
 *
 * @author Tim Enger
 */

public interface IExportableProof {

    /**
     * Full Proof export
     *
     * @param eu
     *            The {@link Export_Util} used.
     * @return The {@link String full proof} of this rule with details.
     */
    String exportProof(Export_Util eu);

    /**
     * Short Proof export (names)
     *
     * @param eu
     *            The {@link Export_Util} used.
     * @return The {@link String short proof} of this rule with less details
     *         (most of the time just the name).
     */
    String exportProofShort(Export_Util eu);
}
