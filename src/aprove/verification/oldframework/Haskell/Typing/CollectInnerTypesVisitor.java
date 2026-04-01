package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Syntax.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor collects the inner types of a class, instance, datadecl or newtype
 * it is used by the kind inference
 */
public class CollectInnerTypesVisitor extends HaskellVisitor {
    Set<HaskellPreType> innerTypes;

    public CollectInnerTypesVisitor(){
        this.innerTypes = new HashSet<HaskellPreType>();
    }

    public Set<HaskellPreType> getInnerTypes(){
       return this.innerTypes;
    }

    @Override
    public HaskellObject caseTypeExp(TypeExp ho){
        this.innerTypes.add(ho.getPreType());
        return ho;
    }
}
