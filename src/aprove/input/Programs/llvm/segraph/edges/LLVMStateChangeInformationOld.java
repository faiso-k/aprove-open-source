package aprove.input.Programs.llvm.segraph.edges;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Parent for all classes holding information about changes between two states connected in an LLVM graph.
 * @author Marc Brockschmidt, cryingshadow
 */
public interface LLVMStateChangeInformationOld extends TRSTermExpressible, SStringExpressible {

    /**
     * NOTE: If the change is not representable as condition in the TRS, "TRUE" is a fine condition.
     * @return A term encoding the change as a condition used in the TRS.
     */
    @Override
    TRSTerm toTerm();

}
