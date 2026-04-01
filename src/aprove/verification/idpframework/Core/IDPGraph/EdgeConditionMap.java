package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;

import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;

/**
 *
 * @author Martin Pluecker
 */
public class EdgeConditionMap extends ConditionMap<IEdge> {

    public EdgeConditionMap(final ItpfFactory itpfFactory,
            final FreshVarGenerator freshVarGenerator) {
        super(itpfFactory, freshVarGenerator);
    }

    public EdgeConditionMap(final ItpfFactory itpfFactory,
        final FreshVarGenerator freshVarGenerator,
        final Map<IEdge, Itpf> source) {
        super(itpfFactory, freshVarGenerator, source);
    }

}
