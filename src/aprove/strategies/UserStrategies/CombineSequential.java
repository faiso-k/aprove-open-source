package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;

@AcceptsStrategiesAsList
public class CombineSequential extends Combine {

    @ParamsViaArgumentObject
    public CombineSequential(Options options) {
        super(options);
    }

    @Override
    public String export(Export_Util o) {
        return o.export("Combine(")+o.exportToEnumeratingText(options.subStrategies, ",")+o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecCombineSequential(options.subStrategies, pos, rti, options);
    }

}
