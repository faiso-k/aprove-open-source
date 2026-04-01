package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * @author christian
 *
 * For easier type checking, edge information which holds information about objects
 * implements this interface
 */
public interface ObjectInformation extends VariableInformation {
    public AbstractVariableReference getRef();
}
