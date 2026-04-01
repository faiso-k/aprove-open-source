package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A root position for a NRIR. A NRIR itself also has a bit denoting changes and
 * a reference name, but we only want to consider the set of original references
 * (in the calling states, causing the NRIR to exist) when comparing the
 * positions of two NRIRs.
 * @author cotto
 */
public final class NonRootIRPosition extends InputRefRootPosition {
    /**
     * For each NRIR-origin (cf. NRIR.sameOrigin()) we only use a single
     * position object.
     */
    private static final Map<Pair<NonRootInputReference, Integer>, NonRootIRPosition> MAP = new LinkedHashMap<>();

    /**
     * The NRIR for which this position is created.
     */
    private final NonRootInputReference ir;

    /**
     * The number of the stack frame containing this reference (most of the
     * times this is 0).
     */
    private final int frameNum;

    /**
     * Create a root position for the given NRIR.
     * @param irParam a NRIR.
     * @param frame the number of the stack frame containing this reference
     * (most of the times this is 0).
     */
    private NonRootIRPosition(final NonRootInputReference irParam, final int frame) {
        this.ir = irParam;
        this.frameNum = frame;
    }

    /**
     * @return a root position for the given NRIR.
     * @param irParam a NRIR.
     * @param frameNum the number of the stack frame containing this reference
     * (most of the times this is 0).
     */
    public static NonRootIRPosition create(final NonRootInputReference irParam, final int frameNum) {
        // equals on NRIRs is weird, so we do a bit of magic here
        NonRootIRPosition result;
        synchronized (NonRootIRPosition.class) {
            for (final Entry<Pair<NonRootInputReference, Integer>, NonRootIRPosition> entry : NonRootIRPosition.MAP.entrySet()) {
                final NonRootInputReference nrir = entry.getKey().x;
                final int frame = entry.getKey().y;
                if (frame == frameNum && nrir.sameOrigin(irParam)) {
                    return entry.getValue();
                }
            }
            for (final Entry<Pair<NonRootInputReference, Integer>, NonRootIRPosition> entry : NonRootIRPosition.MAP.entrySet()) {
                final NonRootInputReference nrir = entry.getKey().x;
                final int frame = entry.getKey().y;
                if (frame == frameNum && nrir.sameOrigin(irParam)) {
                    return entry.getValue();
                }
            }
            result = new NonRootIRPosition(irParam, frameNum);
            final Pair<NonRootInputReference, Integer> pair = new Pair<>(irParam, frameNum);
            NonRootIRPosition.MAP.put(pair, result);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractVariableReference getFromState(
        final State state,
        final boolean failOK,
        final Map<StatePosition, AbstractVariableReference> cache)
    {
        final StackFrame sf = state.getCallStack().get(this.frameNum);
        if (failOK && sf == null) {
            return null;
        }
        final NonRootInputReference nrir = sf.getInputReferences().getNonRootInputReference(this.ir);
        if (failOK && nrir == null) {
            return null;
        }
        return nrir.getReference();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        // this gives the reference name and changed bit information of the first NRIR we put into the map (cf. sameOrigin problem)
        this.ir.toString(sb, null, null, true);
    }
}
