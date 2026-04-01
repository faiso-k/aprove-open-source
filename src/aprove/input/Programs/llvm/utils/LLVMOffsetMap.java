package aprove.input.Programs.llvm.utils;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Give maps from references to sets of pairs of references and BigIntegers a name.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMOffsetMap extends LinkedHashMap<LLVMHeuristicVariable, Set<Pair<LLVMHeuristicVariable, BigInteger>>> {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = -7576009623377327044L;

}