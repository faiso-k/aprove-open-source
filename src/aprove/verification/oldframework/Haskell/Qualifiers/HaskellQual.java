package aprove.verification.oldframework.Haskell.Qualifiers;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * qualifiers are the expressions in do's or list comprehension's
 * they have to implement thier own transformation rules toMonad or toListComp
 */
public interface HaskellQual extends HaskellObject {

   public HaskellExp toMonad(DoCompFactory fac,HaskellExp exp);
   public HaskellExp toListComp(DoCompFactory fac,HaskellExp exp);
}




