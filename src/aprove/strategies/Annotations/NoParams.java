package aprove.strategies.Annotations;

import java.lang.annotation.*;

/**
 * Indicates a class that will be created by the strategy framework without parameters.
 *
 * This is semantically equivalent to annotating the no-args constructor with
 * <code>@ParamsViaArguments({})</code>.
 *
 * @author bearperson
 * @version $Id$
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface NoParams {
}
