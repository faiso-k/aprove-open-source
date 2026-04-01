package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;

@AcceptsStrategiesAsList
public class CombineParallel extends  Combine {

    @ParamsViaArgumentObject
    public CombineParallel(Options options) {
        super(options);
    }

    @Override
    public String export(Export_Util o) {
        return o.export("CombineP(")+o.exportToEnumeratingText(options.subStrategies, ",")+o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecCombineParallel(this.options.subStrategies, pos, rti, options);
    }

}
