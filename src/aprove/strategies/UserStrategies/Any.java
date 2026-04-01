package aprove.strategies.UserStrategies;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import immutables.*;


@AcceptsStrategiesAsList
public class Any extends UserStrategy {

    private final Collection<UserStrategy> strategies;

    @ParamsViaArguments("subStrategies")
    public Any(Collection<UserStrategy> strategies) {
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
        this.strategies = ImmutableCreator.create(strategies);
    }

    @Override
    public String export(Export_Util o) {
        return o.export("Any(")+o.exportToEnumeratingText(this.strategies, ",")+o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecAny(this.strategies, pos, rti);
    }

}
