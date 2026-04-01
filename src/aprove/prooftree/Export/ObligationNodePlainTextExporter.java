package aprove.prooftree.Export;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;

/**
 * Plain text exporter for obligations
 *
 * @author Marc Brockschmidt
 */
public class ObligationNodePlainTextExporter extends ObligationNodeExporter {
    /**
     * Create a new exporter for an obligation from a tree.
     * @param n obligation node to export.
     * @param id unique numeric id of the entry to export.
     * @param exUtil some export helper used to format the nodes.
     */
    public ObligationNodePlainTextExporter(final ObligationNode n, final long id, final Export_Util exUtil) {
        super(n, id, exUtil);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void export() {
        StringBuilder out = this.getOutput();
        ObligationNode obligationNode = this.getObligationNode();
        Export_Util exportUtil = this.getExportUtil();

        out.append(exportUtil.linebreak())
           .append("----------------------------------------")
           .append(exportUtil.linebreak())
           .append(exportUtil.linebreak())
           .append("(")
           .append(this.getNumericId())
           .append(")")
           .append(exportUtil.linebreak());

        if (obligationNode instanceof BasicObligationNode) {
            BasicObligation obligation =
                ((BasicObligationNode) obligationNode).getBasicObligation();
            out.append("Obligation:")
               .append(exportUtil.linebreak())
               .append(obligation.export(exportUtil));
        } else if (obligationNode instanceof JunctorObligationNode) {
            JunctorObligationNode jnode = (JunctorObligationNode) obligationNode;
            if (jnode.getSuccessorCount() == 0) {
                out.append(obligationNode.getRepresentation());
            } else {
                out.append("Complex Obligation (")
                   .append(obligationNode.getRepresentation())
                   .append(")");
            }
            out.append(exportUtil.linebreak());
        }
    }
}
