package aprove.verification.dpframework.IDPProblem.Processors.itpfExecution;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author Martin Pluecker
 */
public class ItpfSchedulerEdgeProof extends ItpfSchedulerProof {

    protected final IdpEdge edge;

    public ItpfSchedulerEdgeProof(IdpEdge edge, Map<IItpfRule, Set<IItpfRule>> ruleGrouping) {
        super(ruleGrouping);
        this.edge = edge;
    }

    public IdpEdge getEdge() {
        return this.edge;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return this.export(o, null, level);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap,
            VerbosityLevel verbosityLevel) {
        StringBuilder sb = new StringBuilder();
        if (this.steps.isEmpty()) {
            sb.append("The edge ");
            sb.append(this.edge.export(o, predefinedMap, verbosityLevel));
            sb.append(" is not modified");
            sb.append(o.linebreak());
        } else {
            sb.append("The itpf formula of the edge ");
            sb.append(this.edge.exportShort(o));
            sb.append(": ");
            sb.append(this.edge.getItpf().export(o, predefinedMap, verbosityLevel));
            sb.append(" is modified as followed:");
            sb.append(o.linebreak());
        }
        this.exportSteps(sb, o, predefinedMap, verbosityLevel);
        return sb.toString();
    }

}
