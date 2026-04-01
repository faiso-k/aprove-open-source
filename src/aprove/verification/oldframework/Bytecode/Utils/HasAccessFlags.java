package aprove.verification.oldframework.Bytecode.Utils;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * Give access to the access flags public/private/protected/static.
 * @author cotto
 */
public interface HasAccessFlags {
    /**
     * @return true iff this is public
     */
    boolean isPublic();

    /**
     * @return true iff this is protected
     */
    boolean isProtected();

    /**
     * @return true iff this is private
     */
    boolean isPrivate();

    /**
     * @return true iff this is static
     */
    boolean isStatic();

    default boolean wasMarkedAsAccessibleBy(ClassName className) {
        return false;
    }

    /**
     * @return the class name declaring this field/method
     */
    ClassName getClassName();
}
