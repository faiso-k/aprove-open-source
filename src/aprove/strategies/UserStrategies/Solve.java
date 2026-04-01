package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;


@AcceptsStrategies("s")
public class Solve extends UserStrategy {

    private final UserStrategy str;
    private final ExecSolve.AcceptableResult acceptable;

    public Solve(UserStrategy s) {
        this(s,ExecSolve.AcceptableResult.WANT_ANY);
    }

    @ParamsViaArguments({"s", "desiredResult"})
    public Solve(UserStrategy s, ExecSolve.AcceptableResult acceptable) {
        this.str = s;
        this.acceptable = acceptable;
    }

    @Override
    public String export(Export_Util o) {
        return o.export("Solve[DesiredResult = " + this.acceptable + "](") + this.str.export(o) + o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecSolve(this.str, this.acceptable, pos, rti);
    }


}
