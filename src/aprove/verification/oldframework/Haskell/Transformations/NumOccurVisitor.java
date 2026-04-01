package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Patterns.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 */
public class NumOccurVisitor extends HaskellVisitor {
     boolean occur = false;

     @Override
    public HaskellObject casePlusPat(PlusPat ho) {
        this.occur = true;
        return ho;
     }

     @Override
    public boolean guardPlusPat(PlusPat ho)                     { return false; }

     @Override
    public HaskellObject caseIntegerLit(IntegerLit ho) {
        this.occur = true;
        return ho;
     }

     @Override
    public HaskellObject caseFloatLit(FloatLit ho) {
        this.occur = true;
        return ho;
     }

     @Override
    public HaskellObject caseCharLit(CharLit ho) {
        this.occur = true;
        return ho;
     }

     public static boolean applyTo(List<HaskellPat> pats)   {
         NumOccurVisitor nov = new NumOccurVisitor();
         List<HaskellPat> res = nov.listWalk(pats,nov);
         return nov.occur;
     }
}
