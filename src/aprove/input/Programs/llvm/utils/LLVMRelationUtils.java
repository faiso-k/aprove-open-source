package aprove.input.Programs.llvm.utils;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Utility methods for relations.
 * @author cryingshadow
 * @version $Id$
 */
public abstract class LLVMRelationUtils {

    /**
     * @param rels A set of relations.
     * @return A term encoding the conjunction of the specified relations.
     */
    public static TRSTerm toTerm(Set<LLVMRelation> rels) {
        final TRSTerm trueTerm =
            TRSTerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getSym());
        return
            ObjectUtils.binaryFold(
                rels,
                trueTerm,
                IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Land, DomainFactory.BOOLEAN),
                new Combinator<LLVMRelation, TRSTerm, FunctionSymbol, TRSTerm>() {

                    @Override
                    public TRSTerm combine(FunctionSymbol connector, LLVMRelation lhs, TRSTerm rhs) {
                        if (trueTerm.equals(rhs)) {
                            return lhs.toTerm();
                        }
                        return TRSTerm.createFunctionApplication(connector, rhs, lhs.toTerm());
                    }

                }
            );
    }

}
