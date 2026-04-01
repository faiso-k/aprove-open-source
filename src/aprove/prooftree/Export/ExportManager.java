/**
 * @author marc
 */
package aprove.prooftree.Export;

import java.io.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;

public abstract class ExportManager {
    /**
     * Purpose of this proof (i.e. termination, complexity, ...)
     */
    protected final String purpose;

    /**
     * Name of the problem we handle (sometimes a filename...)
     */
    protected final String fileName;

    /**
     * Root of the proof tree to export:
     */
    protected final ObligationNode proofTreeRoot;

    /**
     * Export utility helping with the formatting:
     */
    protected Export_Util exportUtil;

    /**
     * Descriptor of the purpose of this proof:
     */
    protected final ProofPurposeDescriptor proofPurposeDescriptor;

    /**
     * Create a new export manager. This abstract class only holds common
     * fields and static methods.
     *
     * @param root Root of the proof tree to export.
     * @param name Name of the problem we handle (sometimes a filename...).
     */
    public ExportManager(final ObligationNode root, final String name) {
        this.proofTreeRoot = root;
        this.fileName = name;
        this.exportUtil = new HTML_Util();

        if (this.proofTreeRoot instanceof BasicObligationNode) {
            this.proofPurposeDescriptor = ((BasicObligationNode) this.proofTreeRoot).getBasicObligation().getProofPurposeDescriptor();
            this.purpose = this.proofPurposeDescriptor.getPurpose();
        } else {
            this.proofPurposeDescriptor = null;
            this.purpose = null;
        }
    }

    /**
     * @return commit ID of the used version of AProVE.
     */
    public static String getCommitID() {
        String commitid = "unknown";
        try {
            final InputStream is = ParallelExportManager.class.getResourceAsStream("/VERSION");
            if (is != null) {
                final byte[] buf = new byte[1024]; // this should be more than enough for the VERSION file *stupid grin*
                final int l = is.read(buf);
                commitid = new String(buf, 0, l, "UTF-8");
            }
        } catch (final IOException e) {
            e.printStackTrace();
        }
        return commitid;
    }

    /**
     * @return Description of the used version of AProVE.
     */
    public String getCommitDescription() {
        return ExportManager.getCommitDescriptionText();
    }

    /**
     * @return Description of the used version of AProVE.
     */
    public static String getCommitDescriptionText() {
        return "AProVE Commit ID: " + ExportManager.getCommitID();
    }
}
