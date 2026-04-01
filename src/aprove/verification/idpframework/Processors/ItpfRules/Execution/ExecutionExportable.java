package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author MP
 */
public interface ExecutionExportable extends IDPExportable {

    public void export(StringBuilder sb,
        Export_Util eu,
        VerbosityLevel verbosityLevel,
        ExecutionStepColorization colors);

    public static abstract class ExecutionExportableSkeleton extends IDPExportable.IDPExportableSkeleton implements ExecutionExportable {

        @Override
        public final void export(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            this.export(sb, eu, verbosityLevel, ExecutionStepColorization.EMPTY);
        }

    }

}
