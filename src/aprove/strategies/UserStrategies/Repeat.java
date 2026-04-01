package aprove.strategies.UserStrategies;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;

@AcceptsStrategies("s")
public class Repeat extends UserStrategy {

    public static final String STAR = "*";
    public static final String PLUS = "+";


    private final UserStrategy str; // the strategy
    private final boolean breadth;  // breadth of depth (parallel or sequential)
    private final int lower;    // lower bound on repetitions
    private final Integer upper;    // upper bound on repetitions, null means no limit

    /**
     * repeat* in non-parallel version
     * @param s
     */
    public Repeat(UserStrategy s) {
        this(s, false);
    }

    /**
     * repeat* in breadth or depth way
     * @param s
     * @param breadth
     */
    public Repeat(UserStrategy s, boolean breadth) {
        this(s, 0, null, breadth);
    }

    /**
     * @param s     - the strategy to be repeated
     * @param lower - lower bound of repetitions
     * @param upper - upper bound of repetitions, null means no limit
     * @param breadth - breadth or depth
     */
    public Repeat(UserStrategy s, int lower, Integer upper, boolean breadth) {
        this.str = s;
        this.breadth = breadth;
        this.lower = lower;
        this.upper = upper;
        if (Globals.useAssertions) {
            if (upper != null) {
                assert (lower <= upper.intValue());
            }
        }
    }

    @ParamsViaArguments({"s", "min", "max", "breadth"})
    public Repeat(UserStrategy s, int min, int max, boolean breadth) {
        this(s, min, max<0 ? null : max, breadth);
    }

    @Override
    public String export(Export_Util o) {
        return o.export("Repeat"+(this.breadth ? "" : "S")+"("+this.lower+","+(this.upper == null ? "*" : this.upper)) +","+this.str.export(o) + o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecRepeat(this.str.getExecutableStrategy(pos, rti), this.str, pos, this.lower, this.upper, this.breadth, rti);
    }


}
