package aprove.verification.oldframework.Haskell;



/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * empty interface that is implemented by HaskellObjects which should be HaskellBeans
 * this means they fullfill the bean convention:
 * empty constructor
 * getter and setter for the important fields
 * (important fields are important for proof export/import)
 */
public interface HaskellBean extends java.io.Serializable {
}
