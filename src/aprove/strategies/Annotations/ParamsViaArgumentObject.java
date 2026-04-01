package aprove.strategies.Annotations;

import java.lang.annotation.*;

/**
 * Indicates a constructor that will be called by the strategy framework.
 *
 * The parameters for this Processor/Solver will be put into an instance
 * of the given class (the "argument class").
 * If no class is given, defaults to the type of the constructor's argument.
 *
 * The argument class should have public fields for any parameter to be set,
 * with the same name as is used in the strategy language
 * (names are case insensitive)
 * For those fields that need additional logic,
 * you can provide a set* method instead.
 *
 * Use this if you have a lot of parameters, as it tends to make inheritance
 * easier: Classes deriving from yours can simply derive their argument class
 * from yours and pass it up via a super() call.
 *
 * @author bearperson
 * @version $Id$
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.CONSTRUCTOR)
public @interface ParamsViaArgumentObject {
    Class<?> value() default void.class;
}
