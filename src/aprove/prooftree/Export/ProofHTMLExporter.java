package aprove.prooftree.Export;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;

/**
 * HTML exporter for obligations
 *
 * @author Marc Brockschmidt
 */
public class ProofHTMLExporter extends ProofExporter {
    /**
     * @param p proof to export.
     * @param i implication of <code>proof</code>.
     * @param id unique numeric id of the entry to export.
     * @param exUtil some export helper used to format the nodes.
     */
    public ProofHTMLExporter(final Proof p, final Implication i, final long id, final Export_Util exUtil) {
        super(p, i, id, exUtil);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void export() {
        StringBuilder out = this.getOutput();
        Proof proof = this.getProof();
        Implication implication = this.getImplication();
        out.append("<div id=\"node")
           .append(this.getNumericId())
           .append("\" class=\"proof\">\n")
           .append("<h3>(")
           .append(this.getNumericId())
           .append(") ")
           .append(proof.getName(NameLength.SHORT))
           .append(" (")
           .append(implication.toString())
           .append(" transformation)</h3>")
           .append(proof.export(this.getExportUtil()))
           .append("</div>\n");
    }
}
