package aprove.verification.oldframework.Bytecode.Merger.StatePosition;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This class represents state positions for the static fields of the program.
 * @author cotto
 */
public final class StaticFieldRootPosition extends RootPosition {
    /**
     * For each field we only use a single position object.
     */
    private static final Map<FieldIdentifier, StaticFieldRootPosition> MAP = new LinkedHashMap<>();

    /**
     * The class name of the class containing the static field.
     */
    private final ClassName className;

    /**
     * The name of the static field.
     */
    private final String fieldName;

    /**
     * Create a new position representing a static field.
     * @param id the identifier for the static field
     */
    private StaticFieldRootPosition(final FieldIdentifier id) {
        this.className = id.getClassName();
        this.fieldName = id.getFieldName();
    }

    /**
     * @return a position representing a static field.
     * @param id the identifier for the static field
     */
    public static StaticFieldRootPosition create(final FieldIdentifier id) {
        StaticFieldRootPosition result = StaticFieldRootPosition.MAP.get(id);
        if (result == null) {
            synchronized (StaticFieldRootPosition.class) {
                result = StaticFieldRootPosition.MAP.get(id);
                if (result == null) {
                    result = new StaticFieldRootPosition(id);
                    StaticFieldRootPosition.MAP.put(id, result);
                }
            }
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
        return state.getStaticFields().get(this.className, this.fieldName);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        sb.append(this.className.toString());
        sb.append('.');
        sb.append(this.fieldName);
    }

    /**
     * @return the className
     */
    public ClassName getClassName() {
        return this.className;
    }

    /**
     * @return the fieldName
     */
    public String getFieldName() {
        return this.fieldName;
    }
}
