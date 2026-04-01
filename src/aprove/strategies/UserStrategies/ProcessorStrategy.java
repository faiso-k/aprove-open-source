package aprove.strategies.UserStrategies;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.verification.dpframework.*;

public class ProcessorStrategy extends UserStrategy {

    private final Processor proc;
    private final String shortName;
    private final String nameAddendum;

    public ProcessorStrategy(Processor proc, String shortName,
            String nameAddendum) {
        this.proc = proc;
        this.shortName = shortName;
        this.nameAddendum = nameAddendum;
    }

    public ProcessorStrategy(Processor proc) {
        this(proc, ParameterManager.getShort(proc), "<from java>");
    }

    @Override
    public String export(Export_Util o) {
        return ParameterManager.getShort(this.proc);
    }

    @Override
    public ExecutableStrategy getExecutableStrategy(BasicObligationNode pos, RuntimeInformation rti) {
        return new ExecProcessorStrategy(this.proc, pos, rti, this.shortName, this.nameAddendum);
    }

    /**
     * Checks if the contained processor is applicable to this obligation and
     * handling mode
     */
    @Override
    public boolean isApplicable(BasicObligation obl) {
        return this.proc.isApplicable(obl);
    }

    // Needed for the diophantine solver
    public Processor getProcessor() {
        return this.proc;
    }


}
