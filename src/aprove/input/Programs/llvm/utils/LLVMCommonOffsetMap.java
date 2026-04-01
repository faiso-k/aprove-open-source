package aprove.input.Programs.llvm.utils;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Give maps from BigIntegers to sets of pairs of references a name.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMCommonOffsetMap
extends LinkedHashMap<BigInteger, Set<Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>>> {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -8879404731418531165L;

}