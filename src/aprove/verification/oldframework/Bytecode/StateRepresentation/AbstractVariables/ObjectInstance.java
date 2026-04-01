package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Parent class of the different object representations supported by AProVE.
 *
 * @author Marc Brockschmidt
 */
public abstract class ObjectInstance extends AbstractVariable {
    /**
     * @param state State in which this access is occurring.
     * @param myRef reference to this instance (can be null if there is no
     *  reference to it yet).
     * @param className name of the class in which to get the field.
     * @param name name of an instance field.
     * @return abstract variable reference to the value of the field
     *  <code>name</code>.
     */
    public abstract AbstractVariableReference getField(final State state,
            final AbstractVariableReference myRef,
            final ClassName className,
            final String name);

    /**
     * @param state State in which this access is occurring.
     * @param myRef reference to this instance (can be null if there is no
     * reference to it yet).
     * @param className name of the class in which to set the field.
     * @param name name of an instance field.
     * @param varRef abstract variable reference to the new value of the field
     *  <code>name</code>.
     * @return information about changes in Defreach annotations that _must_ be regarded
     */
    public abstract Collection<DefiniteReachabilityAnnotationCreation> putField(final State state,
            final AbstractVariableReference myRef,
            final ClassName className,
            final String name,
            final AbstractVariableReference varRef);

    /**
     * @return true if this instance is the NULL instance.
     */
    @Override
    public boolean isNULL() {
        return false;
    }

    /**
     * @return The default value defined in the JVMS for this value type
     */
    public static AbstractVariable getDefaultValue() {
        return ConcreteInstance.NULL;
    }

    public abstract JSONObject toJSON() throws JSONException;
}
