package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;

@AcceptsStrategies("s")
public class Timer extends UserStrategy {

    private final UserStrategy str;
    private final long millis;

    @ParamsViaArguments({"timeout", "s"})
    public Timer(long limitInMillis, UserStrategy s) {
        this.str = s;
        this.millis = limitInMillis;
    }

    @Override
    public String export(Export_Util o) {
        return o.export("Timer("+this.millis+", ") + this.str.export(o) + o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecTimer(this.str, this.millis, pos, rti);
    }


}
