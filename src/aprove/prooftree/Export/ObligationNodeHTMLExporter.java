package aprove.prooftree.Export;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;

/**
 * HTML exporter for obligations
 *
 * @author Marc Brockschmidt
 */
public class ObligationNodeHTMLExporter extends ObligationNodeExporter {
    /**
     * Create a new exporter for an obligation from a tree.
     * @param n obligation node to export.
     * @param id unique numeric id of the entry to export.
     * @param exUtil some export helper used to format the nodes.
     */
    public ObligationNodeHTMLExporter(final ObligationNode n, final long id, final Export_Util exUtil) {
        super(n, id, exUtil);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void export() {
        StringBuilder out = this.getOutput();
        ObligationNode obligationNode = this.getObligationNode();
        String status = ParallelHTMLExportManager.colorForNode(obligationNode);

        out.append("<div id=\"node")
           .append(this.getNumericId())
           .append("\" class=\"obligation\">\n<h3>(")
           .append(this.getNumericId())
           .append(") ");

        if (obligationNode instanceof BasicObligationNode) {
            BasicObligation obligation = ((BasicObligationNode) obligationNode).getBasicObligation();
            out.append("<font class=\"")
               .append(status)
               .append("\">")
               .append("Obligation:</font></h3>")
               .append(obligation.export(this.getExportUtil()));
        } else if (obligationNode instanceof JunctorObligationNode) {
            JunctorObligationNode jnode = (JunctorObligationNode) obligationNode;
            out.append("<font class=\"")
               .append(status)
               .append("\">");
            if (jnode.getSuccessorCount() == 0) {
                out.append(obligationNode.getRepresentation());
            } else {
                out.append("Complex Obligation (")
                   .append(obligationNode.getRepresentation())
                   .append(")");
            }
            out.append("</font></h3>");
        }
        out.append("</div>\n");
    }
}
