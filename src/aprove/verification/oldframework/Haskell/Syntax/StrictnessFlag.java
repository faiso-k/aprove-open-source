package aprove.verification.oldframework.Haskell.Syntax;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * StrictnessFlag is the striktness flag of the type signature of haskell constructors
 * only syntax ist is removed after the strictness is saved in a Boolean Vektor
 * see ConsEntity
 */
public class StrictnessFlag extends HaskellObject.HaskellObjectSkeleton {
      HaskellObject type;

      public StrictnessFlag(HaskellObject type){
          this.type = type;
      }

      public HaskellObject getType(){
          return this.type;
      }

      @Override
    public Object deepcopy(){
          return this.hoCopy(new StrictnessFlag(Copy.deep(this.getType())));
      }

      @Override
    public HaskellObject visit(HaskellVisitor hv){
          HaskellError.output(this,"Strictness flag not allowed in this type");
          this.type = this.walk(this.type,hv);
          return this;
      }

}
