package aprove.verification.idpframework.Core;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Martin Pluecker
 */
public interface IDPExportable extends Exportable {

    public static final VerbosityLevel DEFAULT_LEVEL = VerbosityLevel.HIGH;

    public String export(Export_Util eu, VerbosityLevel verbosityLevel);

    public void export(StringBuilder sb,
        Export_Util eu,
        VerbosityLevel verbosityLevel);

    public static abstract class IDPExportableSkeleton implements IDPExportable {

        @Override
        public final String toString() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public final String export(final Export_Util o) {
            return this.export(o, IDPExportable.DEFAULT_LEVEL);
        }

        @Override
        public final String export(final Export_Util o,
            final VerbosityLevel verbosityLevel) {
            final StringBuilder sb = new StringBuilder();
            this.export(sb, o, verbosityLevel);
            return sb.toString();
        }

    }

}
