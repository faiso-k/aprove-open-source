package aprove.prooftree.Export;

import aprove.prooftree.Export.Utility.*;

/**
 * Parent of all exporter classes. Exporters take an obligation node or proof
 * and render it to a StringBuilder. They are implemented as Runnables to
 * allow for easy parallelization of this rendering process.
 *
 * @author Marc Brockschmidt
 */
public abstract class ProofTreeEntryExporter implements Runnable {
    /**
     * The StringBuilder holding the actual output.
     */
    private final StringBuilder output;

    /**
     * A flag indicating if the export is finished.
     */
    private boolean isExported;

    /**
     * Some numeric ID uniquely identifying this entry of the proof tree:
     */
    private final long numericId;

    /**
     * Some export helper used to format the nodes.
     */
    private Export_Util exportUtil;

    /**
     * Create a fresh exporter.
     * @param id unique numeric id of the entry to export.
     * @param exUtil some export helper used to format the nodes.
     */
    public ProofTreeEntryExporter(final long id, final Export_Util exUtil) {
        this.numericId = id;
        this.exportUtil = exUtil;
        this.output = new StringBuilder();
        this.isExported = false;
    }

    /**
     * Execute this exporter.
     */
    @Override
    public synchronized void run() {
        this.export();
        this.isExported = true;
        this.notifyAll();
    }

    /**
     * Start the actual export process.
     */
    public abstract void export();

    /**
     * Wait for this exporter to finish.
     * @throws InterruptedException when processing was interrupted.
     */
    public synchronized void waitForExport() throws InterruptedException {
        while (!this.isExported) {
            this.wait();
        }
    }

    /**
     * @return the numeric id of the entry to export.
     */
    public long getNumericId() {
        return this.numericId;
    }

    /**
     * @return the export util.
     */
    public Export_Util getExportUtil() {
        return this.exportUtil;
    }

    /**
     * @return the output string builder
     */
    protected StringBuilder getOutput() {
        return this.output;
    }

    /**
     * @return the output
     */
    public String getOutputString() {
        assert (this.isExported) : "Not done with exporting yet, can't output";
        return this.output.toString();
    }
}
