/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Algorithms.UsableRules;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.oldframework.Utility.*;

public class IDPUsableRulesResult extends IDPExportable.IDPExportableSkeleton {

    public static IDPUsableRulesResult create(final Itpf formula) {
        return new IDPUsableRulesResult(formula);
    }

    private final Itpf formula;

    public IDPUsableRulesResult(final Itpf formula) {
        this.formula = formula;
    }

    public Itpf getFormula() {
        return this.formula;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        this.formula.export(sb, eu, verbosityLevel);
    }

}
