package aprove.input.Programs.llvm.internalStructures;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A triple of an abstract state, a map from references to their new lower/upper limits (if these are not equal), and
 * replacements from references to references conducted.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMKnowledgeResult
extends
    Triple<
        LLVMHeuristicState,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>>,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable>
    >
{

    /**
     * @param state The state.
     * @param shrinking Mapping from references to their new lower/upper limits.
     * @param replacements The replacements.
     */
    public LLVMKnowledgeResult(
        LLVMHeuristicState state,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements
    ) {
        super(state, shrinking, replacements);
    }

}
