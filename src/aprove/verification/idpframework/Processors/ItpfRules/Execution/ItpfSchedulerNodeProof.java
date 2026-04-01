package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Martin Pluecker
 */
public class ItpfSchedulerNodeProof extends ItpfSchedulerProof<Itpf, GenericItpfRule<?>> {

    private final INode node;

    public ItpfSchedulerNodeProof(final IDPProblem idp, final INode node,
            final Itpf condition) {
        super(idp, condition, idp.getItpfFactory().createTrue());
        this.node = node;
    }

    public INode getNode() {
        return this.node;
    }

    @Override
    public Pair<Integer, Map<Itpf, Integer>> export(final StringBuilder sb,
        final Export_Util o, final VerbosityLevel verbosityLevel, final int nextExportId) {
        if (this.isEmptyProof()) {
            sb.append("The condition of the node ");
            this.node.export(sb, o, verbosityLevel);
            sb.append(" is not modified");
            sb.append(o.linebreak());
            return new Pair<Integer, Map<Itpf,Integer>>(nextExportId, Collections.<Itpf, Integer>emptyMap());
        } else {
            sb.append("The condition of the node ");
            this.node.export(sb, o, VerbosityLevel.LOW);
            sb.append(" is modified as followed:");
            sb.append(o.linebreak());
            return super.export(sb, o, verbosityLevel, nextExportId);
        }
    }

}
