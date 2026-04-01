package aprove.strategies.UserStrategies;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import immutables.*;


@AcceptsStrategiesAsList
public class AnyK extends UserStrategy {

    private final Integer k;
    private final Collection<UserStrategy> strategies;

    @ParamsViaArguments({"parallelStrategies", "subStrategies"})
    public AnyK(Integer k, Collection<UserStrategy> strategies) {
        if (Globals.useAssertions) {
            // check for all non-null;
            final List<UserStrategy> myList = new Vector<UserStrategy>();
            int n = 0;
            for (final UserStrategy s : strategies) {
                if (s != null) {
                    myList.add(s);
                } else {
                    System.err.println(n+"th str. in any undefined!");
                }
                n++;
            }
            strategies = myList;

            if (k <= 0) {
                System.err.println("invalid k: " + k);
                k = 1;
            }
        }
        this.k = k;
        this.strategies = ImmutableCreator.create(strategies);
    }

    @Override
    public String export(final Export_Util o) {
        return o.export("AnyK(")+ this.k + ", " + o.exportToEnumeratingText(this.strategies, ",")+o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(final BasicObligationNode pos, final RuntimeInformation rti) {
        return new ExecAnyK(this.k, this.strategies, pos, rti);
    }

}
