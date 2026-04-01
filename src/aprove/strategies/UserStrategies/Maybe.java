package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;

@AcceptsStrategies("s")
public class Maybe extends UserStrategy {

    private final UserStrategy str;

    @ParamsViaArguments("s")
    public Maybe(UserStrategy s) {
        this.str = s;
    }

    @Override
    public String export(Export_Util o) {
        return o.export("Maybe(") + this.str.export(o) + o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        UserStrategy alternative = new Repeat(this.str, 0, 1, true);
        return alternative.getExecutableStrategy(pos, rti);
    }


}
