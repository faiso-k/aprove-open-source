package aprove.input.Programs.llvm.internalStructures.expressions;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * An integer constant for LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public interface LLVMConstant extends IntegerConstant, LLVMFunctionApplication, LLVMSimpleTerm {

    @Override
    default Set<? extends LLVMSymbolicVariable> getVariables() {
        return Collections.emptySet();
    }

    @Override
    LLVMConstant negate();

    @Override
    default TRSTerm toTerm() {
        return TRSTerm.createFunctionApplication(FunctionSymbol.create(this.getName(), 0));
    }

}
