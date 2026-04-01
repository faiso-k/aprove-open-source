package aprove.strategies.Annotations;

import java.lang.annotation.*;

/**
 * Annotate a class with this to document it receives "strategy" parameters
 * from the strategy, as in e.g.
 * <pre>HaskellNarrowing[Show = True](termOnHaskell, nontermOnHaskell)</pre>
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface AcceptsStrategies {
    /**
     * The parameter names to which the strategy parameters will be mapped
     */
    String[] value();

    /**
     * If true, strategy can supply less parameters than required,
     * the rest will remain unset.
     */
    boolean optional() default false;
}
