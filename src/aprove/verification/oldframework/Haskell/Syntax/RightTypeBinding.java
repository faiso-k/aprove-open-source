package aprove.verification.oldframework.Haskell.Syntax;



/**
 * @author Stephan Swiderski
 * @version $Id$
 */

/**
 * (x + y :: tau)  is readed as  ((x+y) :: tau)
 * (x $ \x -> e :: tau) is readed as (x $ (\x -> e :: tau))
 * it depends on the right most expression
 * if it is a lambda,let or if the type signature is given to most right term
 * so \x -> let z == z in \ y -> z :: a is readed as \x -> let z == z in \y -> (z :: a)
 * don't be surprised it is real ugly cause it is Haskell
 */
public interface RightTypeBinding {
    /**
     * implemented in Lambda,if,let to handle the type signatures correct
     */
    public void shiftTypeDown(HaskellPreType type);
}