package aprove.verification.oldframework.Haskell;

import java.util.*;

import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class HaskellPR extends Pair<List<Pair<HaskellExp,HaskellExp>>,List<Pair<HaskellExp,HaskellExp>>> {

   public HaskellPR(List<Pair<HaskellExp,HaskellExp>> p,List<Pair<HaskellExp,HaskellExp>> r){
       super(p,r);
   }

   public List<Pair<HaskellExp,HaskellExp>> getP(){
       return this.x;
   }

   public List<Pair<HaskellExp,HaskellExp>> getR(){
       return this.y;
   }
}