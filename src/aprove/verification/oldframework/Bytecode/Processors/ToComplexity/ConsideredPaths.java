package aprove.verification.oldframework.Bytecode.Processors.ToComplexity;

import aprove.prooftree.Export.Utility.*;

public enum ConsideredPaths implements Exportable {

    ALL_PATHS_FROM_START,
    NONTERM_PATHS_AND_PATHS_FROM_START_TO_SINKS;

    @Override
    public String export(Export_Util eu) {
        return this.name().toLowerCase().replace("_", " ");
    }

}