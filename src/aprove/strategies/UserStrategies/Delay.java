package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;

@AcceptsStrategies("s")
public class Delay extends UserStrategy {

    private final UserStrategy str;
    private final long delay;

    @ParamsViaArguments({"delay", "s"})
    public Delay(long delay, UserStrategy s) {
        this.str = s;
        this.delay = delay;
    }

    @Override
    public String export(Export_Util o) {
        return o.export("Delay("+this.delay+", ") + this.str.export(o) + o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecDelay(this.str, this.delay, pos, rti);
    }


}
