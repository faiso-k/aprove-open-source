package aprove.prooftree.Export;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Parent of all proof exporter classes.
 *
 * @author Marc Brockschmidt
 */
public abstract class ProofExporter extends ProofTreeEntryExporter {
    /**
     * Proof to export.
     */
    private final Proof proof;

    /**
     * Implication of the proof to export.
     */
    private final Implication implication;

    /**
     * Create a new exporter for an obligation from a tree.
     * @param p proof to export.
     * @param i implication of <code>proof</code>.
     * @param id unique numeric id of the entry to export.
     * @param exUtil some export helper used to format the nodes.
     */
    public ProofExporter(final Proof p, final Implication i, final long id, final Export_Util exUtil) {
        super(id, exUtil);
        this.proof = p;
        this.implication = i;
    }

    /**
     * @return Proof to export.
     */
    protected Proof getProof() {
        return this.proof;
    }

    /**
     * @return Implication of the proof to export.
     */
    protected Implication getImplication() {
        return this.implication;
    }
}
