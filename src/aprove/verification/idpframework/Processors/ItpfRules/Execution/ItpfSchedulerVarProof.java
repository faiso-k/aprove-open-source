package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Martin Pluecker
 */
public class ItpfSchedulerVarProof<C extends SemiRing<C>> extends ItpfSchedulerProof<Itpf, GenericItpfRule<?>> {

    private final ItpfBoolPolyVar<C> var;

    public ItpfSchedulerVarProof(final IDPProblem idp, final ItpfBoolPolyVar<C> var,
            final Itpf condition) {
        super(idp, condition, idp.getItpfFactory().createTrue());
        this.var = var;
    }

    public ItpfBoolPolyVar<C> getVariable() {
        return this.var;
    }

    @Override
    public Pair<Integer, Map<Itpf, Integer>> export(final StringBuilder sb,
        final Export_Util o, final VerbosityLevel verbosityLevel, final int nextExportId) {
        if (this.isEmptyProof()) {
            sb.append("The condition of the variable ");
            this.var.export(sb, o, verbosityLevel);
            sb.append(" is not modified");
            sb.append(o.linebreak());
            return super.export(sb, o, verbosityLevel, nextExportId);
        } else {
            sb.append("The condition of the variable ");
            this.var.export(sb, o, VerbosityLevel.LOW);
            sb.append(" is modified as followed:");
            sb.append(o.linebreak());
            return super.export(sb, o, verbosityLevel, nextExportId);
        }
    }

}
