package aprove.strategies.Annotations;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface AcceptsStrategiesAsList {
    String value() default "subStrategies";
}
