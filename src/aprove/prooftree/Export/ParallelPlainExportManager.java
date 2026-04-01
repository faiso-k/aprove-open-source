package aprove.prooftree.Export;

import java.io.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;

/**
 * ExportManager for plain proofs.
 *
 * @author Marc Brockschmidt
 */
public class ParallelPlainExportManager extends ParallelExportManager {
    /** Flag indicating if we are trying to export a TRS dump for a lang frontend. */
    private boolean isDumpProofExport = false;

    /**
     * Create a new export manager. This class holds all the data needed for
     * plain text output.
     *
     * @param root Root of the proof tree to export.
     * @param name Name of the problem we handle (sometimes a filename...).
     */
    public ParallelPlainExportManager(final ObligationNode root, final String name) {
        super(root, name);
        this.exportUtil = new PLAIN_Util();
    }

    /**
     * Create a new export manager. This class holds all the data needed for
     * plain text output.
     *
     * @param root Root of the proof tree to export.
     * @param name Name of the problem we handle (sometimes a filename...).
     * @param isDumpProof Flag indicating if we are trying to export a TRS dump for a lang frontend
     */
    public ParallelPlainExportManager(final ObligationNode root, final String name, final boolean isDumpProof) {
        super(root, name);
        this.exportUtil = new PLAIN_Util();
        this.isDumpProofExport = isDumpProof;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void exportStart(final Writer writer) throws IOException {
        writer.append("proof of ");
        writer.append(this.fileName);
        writer.append(this.exportUtil.linebreak());
        writer.append("# ");
        writer.append(this.getCommitDescription());
        writer.append("\n");
        if (this.proofPurposeDescriptor != null && !this.isDumpProofExport) {
            writer.append(this.exportUtil.linebreak());
            writer.append(this.proofPurposeDescriptor.export(this.exportUtil));
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void exportNavigationProofSeparator(final Writer writer) throws IOException {
        writer.append(this.exportUtil.linebreak());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void exportEnd(final Writer writer) throws IOException {
        //We never did nuffin'!
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void exportObligationNode(final StringBuilder navigationBuilder,
            final long numId,
            final String indentation,
            final ObligationNode oblNode,
            final boolean isRootNode) {
        /*
         * I'm sorry for the following code.
         * The idea is that when using AProVE as frontend only translating JBC|Prolog|Haskell
         * to some TRS, we also want to show a proof. To make this work in the usual framework,
         * we use the usual strategy machine for this. This forces us to return "successful"
         * after dumping a TRS. To avoid exporting the ensuing "YES", we use the following hack:
         */
        if (this.isDumpProofExport
            && oblNode instanceof JunctorObligationNode
            && ((JunctorObligationNode) oblNode).getSuccessorCount() == 0
            && "YES".equals(((JunctorObligationNode) oblNode).getRepresentation()))
        {
            //Do nuffin (this is just the last step we don't want to show in a dump export.
        } else {
            //Add the obligation to the exporter job queue:
            this.addExporterJob(new ObligationNodePlainTextExporter(oblNode, numId, this.exportUtil));

            navigationBuilder
                .append(indentation)
                .append("(")
                .append(numId)
                .append(") ")
                .append(oblNode.getRepresentation())
                .append(this.exportUtil.linebreak());
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void exportProof(final StringBuilder navigationBuilder,
            final long numId,
            final String indentation,
            final Proof proof,
            final Implication impl,
            final long consumedTime) {
        //Add the obligation to the exporter job queue:
        this.addExporterJob(new ProofPlainTextExporter(proof, impl, numId, this.exportUtil));

        navigationBuilder.append(indentation)
                         .append("(")
                         .append(numId)
                         .append(") ")
                         .append(proof.getName(NameLength.SHORT))
                         .append(" [")
                         .append(this.exportUtil.export(impl));
        if (Globals.TIMINGS_IN_PROOF_TREE) {
            navigationBuilder.append(", ")
                             .append(this.convertConsumedTime(consumedTime));
        }
        navigationBuilder.append("]")
                         .append(this.exportUtil.linebreak());
    }
}
