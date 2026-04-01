package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;

@AcceptsStrategies("s")
public class WallTimer extends UserStrategy {

    private final UserStrategy str;
    private final long millis;

    @ParamsViaArguments({"timeout", "s"})
    public WallTimer(long limitInMillis, UserStrategy s) {
        this.str = s;
        this.millis = limitInMillis;
    }

    @Override
    public String export(Export_Util o) {
        return o.export("WallTimer("+this.millis+", ") + this.str.export(o) + o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecWallTimer(this.str, this.millis, pos, rti);
    }


}
