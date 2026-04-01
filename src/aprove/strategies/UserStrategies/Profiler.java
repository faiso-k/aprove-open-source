package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;

public class Profiler extends UserStrategy {

    private final UserStrategy str;
    private String filename;
    private String type;

    public static String TYPE_FILE = "\"File\""; // \" is needed here!
    public static String TYPE_DB = "\"DB\"";

    public Profiler(String type, String filename, UserStrategy s) {
        this.str = s;
        this.filename = filename;
        this.type = type;
    }

    @Override
    public String export(Export_Util o) {
        return o.export("Profiler") + this.str.export(o) + o.export(")");
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        if (this.type.equals(Profiler.TYPE_FILE)) {
            return new ExecProfileFile(this.filename, this.str, pos, rti);
        }
        if (this.type.equals(Profiler.TYPE_DB)) {
            try {
                return new ExecProfileDB(this.filename, this.str, pos, rti);
            } catch (UnableToConnectToDatabaseException e) {
                return null;
            }
        }
        return null;
    }
}
