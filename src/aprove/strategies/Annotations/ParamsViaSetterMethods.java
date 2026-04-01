package aprove.strategies.Annotations;

import java.lang.annotation.*;

/**
 * Indicates a constructor that will be called by the strategy framework.
 *
 * This Processor/Solver will be created using the annotated no-args constructor,
 * the parameters will then be set using setter methods.
 *
 * Don't use this for new code.
 * Only use this to indicate that the legacy behavior is intentional
 * for some reason, but be aware that support for this may go away in the future.
 *
 * @author bearperson
 * @version $Id$
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.CONSTRUCTOR)
public @interface ParamsViaSetterMethods {
}
