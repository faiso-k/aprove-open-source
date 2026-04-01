package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import immutables.*;

/**
 *
 * @author MP
 */
public interface ProcessableFormula extends ExecutionExportable, ExecutionMarkable {

    public Set<IVariable<?>> getFreeVariables();

    public Set<ImmutablePair<INode, ImmutableTermSubstitution>> getNodes();

}
