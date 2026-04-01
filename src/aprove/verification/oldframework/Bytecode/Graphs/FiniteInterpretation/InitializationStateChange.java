package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.Globals;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This edge is used whenever the initialization state for some class was
 * changed from the unknown value to some concrete information. When not
 * considering the special case of classes without any initializer, the new
 * state cannot be merged with any previous state due to the conflicting
 * initialization state.
 * @author cotto
 */
public class InitializationStateChange extends EdgeInformation {
    /**
     * Some unique ID.
     */
    private static final long serialVersionUID = -5749739988711779034L;

    /**
     * Collection of changed classes and their new and old init status.
     */
    private final Collection<Triple<ClassName, InitStatus, InitStatus>> newInitStates;

    /**
     * @param newIS collection of changed classes and their new init states.
     */
    public InitializationStateChange(final Collection<Triple<ClassName, InitStatus, InitStatus>> newIS) {
        if (Globals.useAssertions) {
            for (Triple<ClassName, InitStatus, InitStatus> t : newIS) {
                assert(t.y != t.z);
            }
        }
        this.newInitStates = newIS;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getEdgeColor() {
        return "\"#99ff00\"";
    }

    /**
     * @return collection of changed classes and their new new and old init status (in that order).
     */
    public Collection<Triple<ClassName, InitStatus, InitStatus>> getNewInitStates() {
        return this.newInitStates;
    }

    @Override
    public String toString() {
        return newInitStates.toString();
    }
}
