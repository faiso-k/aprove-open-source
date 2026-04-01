package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;


@AcceptsStrategies({"first", "second"})
public class Sequence extends UserStrategy {

    private final UserStrategy first;
    private final UserStrategy second;
    private final boolean parallel;
    private final String alias;

    public Sequence(UserStrategy first, UserStrategy second){
        this(first,second,false);
    }

    @ParamsViaArguments({"first", "second", "parallel"})
    public Sequence(UserStrategy first, UserStrategy second, boolean parallel) {
        this.first = first;
        this.second = second;
        this.parallel = parallel;
        this.alias = null;
    }

    public Sequence(UserStrategy first, String alias, boolean parallel){
        this.first = first;
        this.second = null;
        this.parallel = parallel;
        this.alias = alias;
    }

    @Override
    public String export(Export_Util o) {
        return this.first.export(o)+o.export(this.parallel ? ";" : ":")+ (this.second != null ? this.second.export(o) :this.alias);
    }


    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        UserStrategy second;
        if (this.alias == null) {
            second = this.second;
        } else {
            second = rti.getProgram().lookup(this.alias);
        }
        return new ExecSequence(this.first.getExecutableStrategy(pos,rti),
                second, this.parallel, rti);
    }

}
