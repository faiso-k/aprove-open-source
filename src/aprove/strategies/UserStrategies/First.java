package aprove.strategies.UserStrategies;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import immutables.*;

@AcceptsStrategiesAsList
public class First extends UserStrategy {

    private final ImmutableList<UserStrategy> strs;

    @ParamsViaArguments("subStrategies")
    public First(List<UserStrategy> strs) {
        if (Globals.useAssertions) {
            // check for all non-null;
            int n = 0;
            for (UserStrategy s : strs) {
                n++;
                if (s == null) {
                    System.err.println(n+"th str. in First undefined!");
                    assert(false);
                }
            }
        }
        this.strs = ImmutableCreator.create(strs);
    }

    @Override
    public String export(Export_Util o) {
        String res = o.export("First(");
        if(this.strs != null) {
            res += o.exportToEnumeratingText(this.strs, ",");
        }
        res += o.export(")");
        return res;
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecFirst(this.strs, pos, rti);
    }

}
