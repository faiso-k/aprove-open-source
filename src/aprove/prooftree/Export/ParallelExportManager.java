package aprove.prooftree.Export;

import java.io.*;
import java.util.*;
import java.util.concurrent.atomic.*;

import aprove.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Util.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Logic.*;

/**
 * This abstract class holds all logic needed to traverse the proof tree
 * when exporting it. In the traversal, we directly create the navigational
 * elements that are later displayed. In the same order, we create a List
 * of Runnable instances. After the traversal has been finished, the ThreadPool
 * tools are used to process each of the Runnable instances. The results are
 * then collected and written to the output in the correct order.
 *
 * @author Marc Brockschmidt
 */
public abstract class ParallelExportManager extends ExportManager {
    /**
     * List of proof tree entries that need to be exported.
     */
    private final List<ProofTreeEntryExporter> exporterJobList;

    /**
     * Create a new export manager. This abstract class holds all the logic
     * needed for (parallelized) proof exporting.
     *
     * @param root Root of the proof tree to export.
     * @param name Name of the problem we handle (sometimes a filename...).
     */
    public ParallelExportManager(final ObligationNode root, final String name) {
        super(root, name);
        this.exporterJobList = new LinkedList<ProofTreeEntryExporter>();
    }

    /**
     * Writes a formatted proof to the <code>result</code> writer
     * and flushes <code>result</code>
     * @param result Some writer which will receive the exported tree.
     */
    public void export(final Writer result) throws IOException {
        //Generate the header:
        this.exportStart(result);

        //Generate the navigation and proof export todo list:
        final StringBuilder navigationBuffer = new StringBuilder();
        this.traverseProofTreeRecursively(navigationBuffer,
                new AtomicInteger(0), "", this.proofTreeRoot, true, false);
        result.append(navigationBuffer);

        //Separate the navigation from the actual proofs:
        this.exportNavigationProofSeparator(result);

        // Schedule proof export
        for (final ProofTreeEntryExporter entry : this.exporterJobList) {
            PrioritizableThreadPool.INSTANCE.execute(entry);
        }

        // Collect results
        for (final ProofTreeEntryExporter entry : this.exporterJobList) {
            try {
                entry.waitForExport();
            } catch (final InterruptedException e) {
                throw new RuntimeException("Parallel export interrupted", e);
            }
            result.append(entry.getOutputString());
        }

        this.exportEnd(result);

        // Make sure that the writer actually writes everything
        result.flush();
    }

    /**
     * Output everything we have to <code>System.out</code>.
     */
    public void exportToStdOut() {
        final PrintWriter pw = new PrintWriter(System.out);
        try {
            this.export(pw);
        } catch (final IOException e) {
            // PrintWriter does not throw IOExceptions
        }
        pw.flush();
    }

    /**
     * @return Exported proof tree (as a string)
     */
    public String export() {
        final StringWriter sw = new StringWriter();
        try {
            this.export(sw);
        } catch (final IOException e) {
            // StringWriter does not throw IOExceptions
        }
        return sw.toString();
    }

    /**
     * Traverse the proof tree and try to find a reasonable exportable subset.
     * This means that if we have been able to prove a result, we will only
     * export the needed parts and leave the unsuccesful parts alone.
     *
     * @param navigationBuilder a string builder to which the navigation is
     *  written.
     * @param numId a counter used to hand out unique numeric IDs to the
     *  exported proof tree entries.
     * @param indent the indentation level.
     * @param currentObl the currently handled obligation.
     * @param isRoot boolean flag indicating if we are the root of our tree.
     * @param indentRight boolean flag indicating if we need to indent in this
     *  step.
     */
    private void traverseProofTreeRecursively(final StringBuilder navigationBuilder,
            final AtomicInteger numId, String indent, ObligationNode currentObl,
            boolean isRoot, boolean indentRight) {
        /*
         * To avoid very deep recursion, we mix an iterative and recursive
         * approach. We work on each node. Whenever there is more than one
         * successor, we call the method again for each successor. If there
         * is only successor, we jump back to beginning of the method and
         * start over.
         */
        ITERATIVE_LOOP: while (true) {
            //Export the current node:
            this.exportObligationNode(navigationBuilder, numId.longValue(),
                    indent, currentObl, isRoot);

            //If we have no children, stop:
            if (currentObl.getSuccessorCount() == 0) {
                return;
            }

            //In DEBUG modes, we export all children:
            boolean mustExportAllChildren = !Globals.DEBUG_NONE || (currentObl instanceof JunctorObligationNode);
            final boolean haveMultipleChildren = (currentObl.getSuccessorCount() > 1);

            if (indentRight || (mustExportAllChildren && haveMultipleChildren)) {
                indent = indent + "    ";
            }

            //For basic obligation, export all needed proofs and new obligations:
            if (currentObl instanceof BasicObligationNode) {
                final BasicObligationNode curBasicObl = (BasicObligationNode) currentObl;

                List<ObligationNodeChild> provingChildren = Collections.emptyList();
                if (haveMultipleChildren) {
                    provingChildren = curBasicObl.getProvingChildren();
                }

                //If there is no proving child, also export all children:
                mustExportAllChildren |= (provingChildren.isEmpty());

                if (mustExportAllChildren || provingChildren.size() > 1) {
                    List<ObligationNodeChild> toExport = provingChildren.size() > 1 ? provingChildren : curBasicObl.getSuccessors();
                    for (final ObligationNodeChild child : toExport) {
                        this.exportProof(navigationBuilder,
                                numId.incrementAndGet(), indent,
                                child.getProof(),
                                child.getImplication(),
                                child.getConsumedTime());
                        numId.incrementAndGet();
                        this.traverseProofTreeRecursively(navigationBuilder,
                                numId, indent, child.getNewObligation(), false,
                                haveMultipleChildren);
                    }
                    return;
                } else {
                    ObligationNodeChild provingChild = provingChildren.get(0);
                    this.exportProof(navigationBuilder,
                            numId.incrementAndGet(), indent,
                            provingChild.getProof(),
                            provingChild.getImplication(),
                            provingChild.getConsumedTime());
                    numId.incrementAndGet();
                    currentObl = provingChild.getNewObligation();
                    indentRight = false;
                    isRoot = false;
                    continue ITERATIVE_LOOP;
                }
            } else if (currentObl instanceof JunctorObligationNode) {
                final JunctorObligationNode curJuncObl = (JunctorObligationNode) currentObl;
                if (haveMultipleChildren) {
                    for (final ObligationNode child : curJuncObl.getChildren()) {
                        numId.incrementAndGet();
                        this.traverseProofTreeRecursively(navigationBuilder,
                                numId, indent, child, false, true);
                    }
                    return;
                } else {
                    numId.incrementAndGet();
                    currentObl = curJuncObl.getChildren().get(0);
                    indentRight = false;
                    isRoot = false;
                    continue ITERATIVE_LOOP;
                }
            } else {
                throw new NotYetImplementedException("Don't know obligation type " + currentObl.getClass());
            }
        }
    }

    /**
     * Export an obligation node.
     *
     * @param navigationBuilder StringBuilder holding what will later become
     *  the navigational element of the exported proof tree.
     * @param numId numeric ID of the element to export.
     * @param indentation current indentation (used in the navigation).
     * @param oblNode the obligation node to export.
     * @param isRootNode flag indicating whether this node is at the root.
     */
    protected abstract void exportObligationNode(final StringBuilder navigationBuilder,
            final long numId,
            final String indentation,
            final ObligationNode oblNode,
            final boolean isRootNode);

    /**
     * Export a proof.
     *
     * @param navigationBuilder StringBuilder holding what will later become
     *  the navigational element of the exported proof tree.
     * @param numId numeric ID of the element to export.
     * @param indentation current indentation (used in the navigation).
     * @param proof the proof to export.
     * @param impl the implication of this proof.
     * @param consumedTime the time consumed by the processor.
     */
    protected abstract void exportProof(final StringBuilder navigationBuilder,
            final long numId,
            final String indentation,
            final Proof proof,
            final Implication impl,
            final long consumedTime);

    /**
     * Export prequel to the proof output (i.e. HTML head or things like that)
     * @param writer Some writer to which the output is going
     * @throws IOException in case the writer is unhappy
     */
    protected abstract void exportStart(final Writer writer) throws IOException;

    /**
     * Export separator between navigation and actual proof output
     * @param writer Some writer to which the output is going
     * @throws IOException in case the writer is unhappy
     */
    protected abstract void exportNavigationProofSeparator(final Writer writer) throws IOException;

    /**
     * Export end of the proof output (i.e. HTML end or things like that)
     * @param writer Some writer to which the output is going
     * @throws IOException in case the writer is unhappy
     */
    protected abstract void exportEnd(final Writer writer) throws IOException;

    /**
     * @param ex some exporter job we need to handle when exporting this tree.
     */
    protected void addExporterJob(final ProofTreeEntryExporter ex) {
        this.exporterJobList.add(ex);
    }

    /**
     * Converts time consumed into string
     * @param consumedTime the timed consumed
     */
    protected String convertConsumedTime(final long consumedTime) {
        if (consumedTime >= 10000) {
            // convert to seconds
            return Math.round(consumedTime / 100.0) / 10.0 + " s";
        } else {
            // milli seconds
            return consumedTime + " ms";
        }
    }
}
