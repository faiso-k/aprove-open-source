package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse;

import aprove.strategies.Annotations.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.EdgeProviders.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.PathGenerators.*;

/**
 * @author Martin Pluecker
 */
public class InfPathCollapse extends AbstractPathCollapse {

    @ParamsViaArguments(value = { "maxEdgeGain" })
    public InfPathCollapse(final float maxEdgeGain) {
        super("InfPathCollapse", new CollapsableInfEdgesProvider(), new NodeCollapsingPathGenerator(),maxEdgeGain);
    }

}
