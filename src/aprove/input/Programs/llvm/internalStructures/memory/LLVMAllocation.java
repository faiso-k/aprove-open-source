package aprove.input.Programs.llvm.internalStructures.memory;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * An allocation is an immutable pair of symbolic variables.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMAllocation extends ImmutablePair<LLVMSimpleTerm, LLVMSimpleTerm> implements Substitutable {

    /**
     * @param lower The lower bound of the allocation.
     * @param upper The upper bound of the allocation.
     */
    public LLVMAllocation(LLVMSimpleTerm lower, LLVMSimpleTerm upper) {
        super(lower, upper);
    }

	@Override
	public LLVMAllocation applySubstitution(Substitution sigma) {
		Expression lowerExpression = x.applySubstitution(sigma);
		Expression upperExpression = y.applySubstitution(sigma);
		
		if(!(lowerExpression instanceof LLVMSimpleTerm && upperExpression instanceof LLVMSimpleTerm))
			return null;
		
		return new LLVMAllocation((LLVMSimpleTerm) lowerExpression, (LLVMSimpleTerm) upperExpression);
				
	}

}
