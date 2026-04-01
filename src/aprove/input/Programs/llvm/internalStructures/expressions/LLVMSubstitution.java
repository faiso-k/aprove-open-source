package aprove.input.Programs.llvm.internalStructures.expressions;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Replaces LLVMSymbolicVariables by LLVMTerms.
 * @author cryingshadow
 * @version $Id$
 */
public interface LLVMSubstitution extends ImmutableSubstitution {

    /**
     * @param sigma Some substitution as map.
     * @return The corresponding ImmutableSubstitution.
     */
    public static LLVMSubstitution toSubstitution(
        Map<? extends LLVMSymbolicVariable, ? extends LLVMTerm> sigma
    ) {
        // cannot avoid code duplication since generics are just broken
        final ImmutableMap<? extends LLVMSymbolicVariable, ? extends LLVMTerm> map = ImmutableCreator.create(sigma);
        return
            new LLVMSubstitution() {

                @Override
                public LLVMTerm substitute(LLVMSymbolicVariable v) {
                    if (map.containsKey(v)) {
                        return map.get(v);
                    }
                    return v;
                }

                @Override
                public ImmutableMap<? extends LLVMSymbolicVariable, ? extends LLVMTerm> toLLVMMap() {
                    return map;
                }

            };
    }

    /**
     * @param v Some LLVMRerefence.
     * @return The LLVMTerm to substitute the specified LLVMReference.
     */
    LLVMTerm substitute(LLVMSymbolicVariable v);

    @Override
    default LLVMTerm substitute(Variable v) {
        return this.substitute((LLVMSymbolicVariable)v);
    }

    /**
     * @return A Map representation of this LLVMSubstitution.
     */
    ImmutableMap<? extends LLVMSymbolicVariable, ? extends LLVMTerm> toLLVMMap();

    @Override
    default ImmutableMap<? extends Variable, ? extends Expression> toMap() {
        return this.toLLVMMap();
    }

}
