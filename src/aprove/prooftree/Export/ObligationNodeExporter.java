package aprove.prooftree.Export;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;

/**
 * Parent of all obligation exporter classes.
 *
 * @author Marc Brockschmidt
 */
public abstract class ObligationNodeExporter extends ProofTreeEntryExporter {
    /**
     * Obligation node to export.
     */
    private final ObligationNode obligationNode;

    /**
     * Create a new exporter for an obligation from a tree.
     * @param n obligation node to export.
     * @param id unique numeric id of the entry to export.
     * @param exUtil some export helper used to format the nodes.
     */
    public ObligationNodeExporter(final ObligationNode n, final long id, final Export_Util exUtil) {
        super(id, exUtil);
        this.obligationNode = n;
    }

    /**
     * @return Obligation node to export.
     */
    protected ObligationNode getObligationNode() {
        return this.obligationNode;
    }
}
