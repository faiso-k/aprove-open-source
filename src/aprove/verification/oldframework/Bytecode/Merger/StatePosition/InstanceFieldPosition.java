package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class represents state positions for the static fields in the program.
 * @author cotto
 */
public final class InstanceFieldPosition extends NonRootPosition {
    /**
     * For each field and predecessor we only use a single position object.
     */
    private static final Map<Pair<StatePosition, FieldIdentifier>, InstanceFieldPosition> MAP =
        new LinkedHashMap<Pair<StatePosition, FieldIdentifier>, InstanceFieldPosition>();

    /**
     * The class name of the class containing the static field.
     */
    private final ClassName className;

    /**
     * The name of the static field.
     */
    private final String fieldName;

    /**
     * Create a new position representing an instance field.
     * @param prev the predecessing state position
     * @param id the field identifier
     */
    private InstanceFieldPosition(final StatePosition prev,
            final FieldIdentifier id) {
        super(prev);
        assert (id != null);
        assert (id.getFieldName() != null);
        assert (id.getClassName() != null);
        this.className = id.getClassName();
        this.fieldName = id.getFieldName();
    }

    /**
     * @return a position representing an instance field.
     * @param prev the predecessing state position
     * @param id the field identifier
     */
    public static InstanceFieldPosition create(final StatePosition prev,
        final FieldIdentifier id) {
        final Pair<StatePosition, FieldIdentifier> pair =
            new Pair<StatePosition, FieldIdentifier>(prev, id);
        InstanceFieldPosition result = InstanceFieldPosition.MAP.get(pair);
        if (result == null) {
            synchronized (InstanceFieldPosition.class) {
                result = InstanceFieldPosition.MAP.get(pair);
                if (result == null) {
                    result = new InstanceFieldPosition(prev, id);
                    InstanceFieldPosition.MAP.put(pair, result);
                }
            }
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected AbstractVariableReference getFromState(final AbstractVariable prevVar,
        final AbstractVariableReference prevRef,
        final State state) throws PositionDoesNotExistException {
        if (prevVar == null || prevVar.isNULL()
            || !(prevVar instanceof ConcreteInstance)) {
            throw PositionDoesNotExistException.INSTANCE;
        }
        final ConcreteInstance instance = (ConcreteInstance) prevVar;
        final AbstractVariableReference fieldRef =
            instance.getField(this.className, this.fieldName, true);
        if (fieldRef == null) {
            throw PositionDoesNotExistException.INSTANCE;
        }
        return fieldRef;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected AbstractVariableReference getReferencesOnPath(final AbstractVariable prevVar,
            final AbstractVariableReference prevRef, final State state,
            final Collection<AbstractVariableReference> result) {
        assert (prevVar instanceof ConcreteInstance);
        final ConcreteInstance instance = (ConcreteInstance) prevVar;
        final AbstractVariableReference nextRef =
            instance.getField(this.className, this.fieldName);
        result.add(nextRef);
        return nextRef;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public HeapEdge getHeapEdge() {
        return new InstanceFieldEdge(this.className, this.fieldName);
    }

    /**
     * @return the field identifier corresponding to this position
     */
    public FieldIdentifier getFieldId() {
        return new FieldIdentifier(this.className, this.fieldName);
    }

    @Override
    public void toString(final StringBuilder sb) {
        super.toString(sb);
        sb.append('.');
        sb.append(this.className.toString());
        sb.append('.');
        sb.append(this.fieldName);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    NonRootPosition getCopyWithOtherPredecessor(final StatePosition newPred) {
        return InstanceFieldPosition.create(newPred, new FieldIdentifier(
            this.className, this.fieldName));
    }
}
