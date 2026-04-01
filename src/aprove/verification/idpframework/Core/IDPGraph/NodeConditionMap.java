package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;

import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;

/**
 *
 * @author Martin Pluecker
 */
public class NodeConditionMap extends ConditionMap<INode> {

    public NodeConditionMap(final ItpfFactory itpfFactory,
            final FreshVarGenerator freshVarGenerator) {
        super(itpfFactory, freshVarGenerator);
    }

    public NodeConditionMap(final ItpfFactory itpfFactory,
        final FreshVarGenerator freshVarGenerator,
        final Map<INode, Itpf> source) {
        super(itpfFactory, freshVarGenerator, source);
    }
}
