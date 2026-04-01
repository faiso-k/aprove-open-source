package aprove.verification.oldframework.Haskell.Typing;

import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * only BasicTerms (Apply,Var,Cons) are HaskellTypes;
 */
public interface HaskellType extends BasicTerm {

    public static class Tools implements java.io.Serializable {

        public Cons Arrow; // = new Cons(new Sym("->"));
        public Cons Star; //  = new Cons(new Sym("*"));

        public Tools(Prelude prelude){
            this.Arrow = prelude.getKindArrow();
            this.Star = prelude.getKindStar();
        }

    }
}
