package aprove.prooftree.Export;

import java.io.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;

/**
 * ExportManager for HTML files using CSS.
 * @author Marc Brockschmidt
 */
public class ParallelHTMLExportManager extends ParallelExportManager {
    /**
     * @param oblNode some obligation node
     * @return color String encoding the truth value of <code>oblNode</code>
     */
    public static String colorForNode(final ObligationNode oblNode) {
        switch (oblNode.getTruthValue().toColor()) {
            case GREEN   : return "color_green";
            case RED    : return "color_red";
            case YELLOW : return "color_yellow";
            case BLUE: return "color_blue";
            default    : return "color_black";
        }
    }

    /**
     * Create a new export manager. This class holds all the data needed for
     * HTML output.
     *
     * @param root Root of the proof tree to export.
     * @param name Name of the problem we handle (sometimes a filename...).
     */
    public ParallelHTMLExportManager(final ObligationNode root, final String name) {
        super(root, name);
        this.exportUtil = new HTML_Util();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void exportStart(final Writer writer) throws IOException {
        writer.append(ExportTemplates.PROOF_HEAD_START);
        writer.append(ExportTemplates.STYLESHEET);
        if (!Options.embedHtmlProof) {
            writer.append(ExportTemplates.STYLE_FULLSCREEN);
        }
        writer.append("<title>\n");
        if (this.purpose != null) {
            writer.append(this.purpose);
            writer.append(" ");
        }
        writer.append("proof of ");
        writer.append(this.fileName);
        writer.append(ExportTemplates.HEAD_END);
        writer.append("<body id=\"embbody\">");
        writer.append("<!-- ");
        writer.append(this.getCommitDescription());
        writer.append(" -->\n");
        writer.append("<div class=\"embedding_pane\">\n");
        writer.append("<div class=\"navigation_pane\">\n");
        writer.append("<div class=\"navigation\">\n");
        if (this.proofPurposeDescriptor != null) {
            writer.append(this.exportUtil.linebreak());
            writer.append(this.proofPurposeDescriptor.export(this.exportUtil));
        }
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected void exportNavigationProofSeparator(final Writer writer) throws IOException {
        writer.append("</div></div>\n");
        writer.append("\n<div class=\"proof_pane\">\n");
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected void exportEnd(final Writer writer) throws IOException {
        if (!Options.embedHtmlProof) {
            writer.append(ExportTemplates.RENDERDOT_SCRIPT);
            writer.append(ExportTemplates.BODY_CLOSE);
            writer.append(ExportTemplates.HTML_CLOSE);
        } else {
            writer.append("</div>\n");
            writer.append("</div>\n");
        }
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

        //Add the obligation to the exporter job queue:
        this.addExporterJob(new ObligationNodeHTMLExporter(oblNode, numId, this.exportUtil));

        //Create the navigation elements and append them:
        final String status = ParallelHTMLExportManager.colorForNode(oblNode);

        navigationBuilder.append(ExportTemplates.PRE_OPEN)
                         .append(indentation);
        // Put an edge in front of the entry for non-root nodes:
        if (!isRootNode) {
            navigationBuilder.append(ExportTemplates.EDGE);
        }
        navigationBuilder.append("<a class=\"")
                         .append(status)
                         .append("\" href=\"#node")
                         .append(numId)
                         .append("\">")
                         .append(numId)
                         .append(" ")
                         .append(oblNode.getRepresentation())
                         .append("</a>")
                         .append(ExportTemplates.PRE_CLOSE)
                         .append("\n");
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
        this.addExporterJob(new ProofHTMLExporter(proof, impl, numId, this.exportUtil));

        navigationBuilder.append(ExportTemplates.PRE_OPEN)
                         .append(indentation);
        // Put an edge in front of the entry for non-root nodes:
        navigationBuilder.append(ExportTemplates.EDGE);
        navigationBuilder.append("<a class=\"color_black\" href=\"#node")
                         .append(numId)
                         .append("\">")
                         .append(numId)
                         .append(" ")
                         .append(proof.getName(NameLength.SHORT))
                         .append(" (")
                         .append(impl.export(this.exportUtil));
        if (Globals.TIMINGS_IN_PROOF_TREE) {
            navigationBuilder.append(", ")
                             .append(this.convertConsumedTime(consumedTime));
        }
        navigationBuilder.append(")</a>")
                         .append(ExportTemplates.PRE_CLOSE)
                         .append("\n");
    }
}
