package aprove.strategies.UserStrategies;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;

@AcceptsStrategiesAsList
public class AnyDelay extends UserStrategy {

    private final long delay;
    private final Collection<UserStrategy> strategies;

    @ParamsViaArguments({"delay", "subStrategies"})
    public AnyDelay(long delay, Collection<UserStrategy> strategies) {
        if (Globals.useAssertions) {
            // check for all non-null;
            List<UserStrategy> myList = new Vector<UserStrategy>();
            int n = 0;
            for (UserStrategy s : strategies) {
                if (s != null) {
                    myList.add(s);
                } else {
                    System.err.println(n+"th str. in any undefined!");
                }
                n++;
            }
            strategies = myList;
        }
        this.delay = delay;
        this.strategies = strategies;
    }

    @Override
    public String export(Export_Util o) {
        return o.export("AnyDelay(" + this.delay +", ") + o.exportToEnumeratingText(this.strategies, ",") + o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecAnyDelay(this.delay, this.strategies, pos, rti);
    }


}
