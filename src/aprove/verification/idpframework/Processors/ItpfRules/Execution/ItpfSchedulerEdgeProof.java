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
public class ItpfSchedulerEdgeProof extends ItpfSchedulerProof<Itpf, GenericItpfRule<?>> {

    private final IEdge edge;
    private final IDependencyGraph graph;

    public ItpfSchedulerEdgeProof(final IDPProblem idp, final IEdge edge,
            final Itpf condition) {
        super(idp, condition, idp.getItpfFactory().createTrue());
        this.graph = idp.getIdpGraph();
        this.edge = edge;
    }

    public IDependencyGraph getGraph() {
        return this.graph;
    }

    public IEdge getEdge() {
        return this.edge;
    }

    @Override
    public Pair<Integer, Map<Itpf, Integer>> export(final StringBuilder sb,
        final Export_Util o, final VerbosityLevel verbosityLevel, final int nextExportId) {
        if (this.isEmptyProof()) {
            sb.append("The edge ");
            this.edge.export(sb, o, verbosityLevel);
            sb.append(" is not modified");
            sb.append(o.linebreak());
            return super.export(sb, o, verbosityLevel, nextExportId);
        } else {
            sb.append("The itpf formula of the edge ");
            this.edge.export(sb, o, VerbosityLevel.LOW);
            sb.append(" is modified as followed:");
            sb.append(o.linebreak());
            return super.export(sb, o, verbosityLevel, nextExportId);
        }
    }

}
