package aprove.strategies.UserStrategies;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;

public class VariableStrategy extends UserStrategy implements EagerlyCheckable {

    private final String name;

    public VariableStrategy(String name) {
        this.name = name;
    }

    @Override
    public String export(Export_Util o) {
        return o.export(this.name);
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        UserStrategy str = rti.getProgram().lookup(this.name);
        if (Globals.PROFILING) {
            // Wrap into something that logs the time spent in this part of the strategy
            return new ExecSimpleProfile(this.name, str, pos, rti);
        } else {
            return str.getExecutableStrategy(pos, rti);
        }
    }

    @Override
    public void check(StrategyProgram program) {
        try {
            program.lookup(this.name);
        } catch (IllegalArgumentException noSuchName) {
            program.reportProblem("unresolved reference to substrategy '" + this.name + "' found!");
        }
    }

}
