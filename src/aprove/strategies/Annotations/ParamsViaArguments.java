package aprove.strategies.Annotations;

import java.lang.annotation.*;

/**
 * Indicates a constructor that will be called by the strategy framework.
 *
 * The parameters for this Processor/Solver will be passed as arguments,
 * in the order they appear in the annotation parameter.
 * You have to specify the names as they appear in the strategy.
 * (We cannot use the java identifier names as they are no longer available
 * at runtime)
 *
 * This method can be used if you only have few parameters,
 * as it is most straightforward and easy to understand.
 * If you have lots of parameters,
 * consider using {@link ParamsViaArgumentObject} instead.
 *
 * @author bearperson
 * @version $Id$
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.CONSTRUCTOR)
public @interface ParamsViaArguments {
    String[] value();
}
