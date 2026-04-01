package aprove.prooftree.Export;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Plain text exporter for obligations
 *
 * @author Marc Brockschmidt
 */
public class ProofPlainTextExporter extends ProofExporter {
    /**
     * @param p proof to export.
     * @param i implication of <code>proof</code>.
     * @param id unique numeric id of the entry to export.
     * @param exUtil some export helper used to format the nodes.
     */
    public ProofPlainTextExporter(final Proof p, final Implication i, final long id, final Export_Util exUtil) {
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
        Export_Util exportUtil = this.getExportUtil();

        out.append(exportUtil.linebreak())
           .append("----------------------------------------")
           .append(exportUtil.linebreak())
           .append(exportUtil.linebreak())
           .append("(")
           .append(this.getNumericId())
           .append(") ")
           .append(proof.getName(NameLength.SHORT))
           .append(" (")
           .append(implication.toString())
           .append(")")
           .append(exportUtil.linebreak())
           .append(proof.export(exportUtil));
    }
}
