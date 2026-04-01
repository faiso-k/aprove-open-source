package aprove.prooftree.Obligations;

import java.util.*;
import java.util.concurrent.atomic.*;

import aprove.api.prooftree.*;
import aprove.prooftree.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.CPF.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * The nodes of our proof tree, representing simple obligations of various
 * types and junctors that in turn depend on other obligations.
 * @author thiemann
 */
public abstract class ObligationNode
implements TruthValueListener, Exportable, XMLProofExportable, CPFObligationNode, HasNonterminatingTerm {

    /**
     * Counter providing unique numeric IDs for all of our obligations.
     */
    private static final AtomicInteger OBLIGATION_ID_COUNTER = new AtomicInteger(1);

    /**
     * @return a string serving as unique ID (built from
     *  <code>ObligationNode.OBLIGATION_ID_COUNTER</code>)
     */
    public static final String getNextObligationId() {
        return "obl-"+ObligationNode.OBLIGATION_ID_COUNTER.getAndIncrement();
    }

    /**
     * Depth of this node in the proof tree.
     */
    private int depth = 0;

    /**
     * Listeners interested in changes in the truth value of the encapsulated
     * obligation.
     */
    private final Collection<TruthValueListener> truthListeners;

    /**
     * Creates a new node and initializes a new, empty listener collection.
     */
    protected ObligationNode() {
        this.truthListeners = new LinkedHashSet<TruthValueListener>();
    }

    /**
     * @param listener new listener interested in truth value changes in this
     *  node.
     */
    public synchronized void addTruthValueListener(final TruthValueListener listener) {
        this.truthListeners.add(listener);
    }

    /**
     * Checks the proof from this node to all ends with CeTA.
     * @param filename The filename where the CPF should be stored.
     * @return the result + stdout and stderr from ceta
     *  (both stdout and stderr may be null, if problems occurred
     *   when trying to execute ceta)
     */
    public abstract Triple<CPFCheckResult, String, String> checkProof(String filename);

    /**
     * @return depth of this node in the proof tree.
     */
    public int getDepth() {
        return this.depth;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Proofs.HasNonterminatingTerm#getNonterminatingTerm()
     */
    @Override
    public abstract TRSTerm getNonterminatingTerm();

    /**
     * @return string representation of this obligation (such as "QDP", "QTRS")
     */
    public abstract String getRepresentation();

    /**
     * @return number of successors this obligation node has.
     */
    public abstract int getSuccessorCount();

    /**
     * @return truth value known for this obligation.
     */
    public abstract TruthValue getTruthValue();

    /**
     * @return true iff the truth value is not MAYBE but something useful
     */
    public boolean isTruthValueKnown() {
        return !this.getTruthValue().isCompletelyUnknown();
    }

    /**
     * @return True iff there are some certifiable techniques which can be applied to this obligation. False otherwise.
     */
    public abstract boolean offersCertifiableTechniques();

    /**
     * Print non-termination witness to the file at the given path.
     * @param file The path to the file.
     */
    public abstract void printGraphmlWitness(String file);

    /**
     * (Re)propagate truth values through the proof tree. Only used when
     * deserializing a proof tree.
     */
    @Deprecated
    public abstract void recursiveRepropagateTruthValues();

    /**
     * @param depth new depth of this node in the proof tree.
     *  Will be propagated accordingly through the whole subtree.
     */
    public void setDepth(final int depth) {
        this.depth = depth;
    }

    /**
     * Informs all interested listeners that we changed our truth value.
     *
     * @param value new truth value
     */
    protected synchronized void informTruthValueListeners(final TruthValue value) {
        for (final TruthValueListener listener : this.truthListeners) {
            listener.truthValueChanged(value, this);
        }
    }

    /**
     * This is a hack which is needed for partial certification with lower bounds.
     * If we have a lower and an upper bound, then we have multiple proving children.
     * This is currently not supported and requires several changes. Since we are
     * running out of time w.r.t. a paper deadline, we use the following workaround for
     * the moment: Just drop the lower bound and take care that all lower bound proofs
     * are counted as unknown proofs via this method.
     */
    public abstract void noteUnknownLowerBoundsProofs(CPFExportStatistic statistics);
}
