package aprove.verification.oldframework.Haskell;

 /**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * creates nice names for type variables
 */
public class TyVarNameGenerator extends NameGenerator{
   private static final String names = "abcdefgh";
   int count;

   public TyVarNameGenerator(){
       this.count = 0;
   }

   @Override
public String createNewNameFor(Object o){
       int cur = this.count;
       this.count++;
       String nname = "";
       do {
           int val = cur % TyVarNameGenerator.names.length();
           nname = TyVarNameGenerator.names.charAt(val)+nname;
           cur = cur - val;
           cur = cur / TyVarNameGenerator.names.length();
       } while (cur>0);
       return nname;
   }

}

