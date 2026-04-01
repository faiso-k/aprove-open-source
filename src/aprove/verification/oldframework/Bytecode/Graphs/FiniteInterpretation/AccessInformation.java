package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

public interface AccessInformation extends VariableInformation {

    FieldAccessRW getAccessType();

    AbstractVariableReference getAccessedRef();

}
