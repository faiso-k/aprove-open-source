package aprove.verification.oldframework.Typing;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;


/**
 * TCModifier modifies type contexts, type definitions, type assumptions,
 * types and terms if applied.
 * Abstract classes implementing this interface taking over the task
 * to reach all the types, type definitions, type assumptions and the type context.
 * @author Stephan Swiderski
 * @version $Id$
 */
public interface TCModifier extends CoarseGrainedTermVisitor {
    public void caseType(Type t);
    public void caseSetOfTypes(Set<Type> t);
    public void caseTypeDefinition(TypeDefinition td);
    public void caseTypeAssumption(TypeAssumption ta);
    public void caseTypeContext(TypeContext tct);
}
