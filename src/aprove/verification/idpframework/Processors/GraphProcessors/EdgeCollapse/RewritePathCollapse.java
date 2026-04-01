package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse;

import aprove.strategies.Annotations.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.EdgeProviders.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.PathGenerators.*;

/**
 * @author Martin Pluecker
 */
public class RewritePathCollapse extends AbstractPathCollapse {

    @ParamsViaArguments(value = { "maxEdgeGain" })
    public RewritePathCollapse(final float maxEdgeGain) {
        super("RewritePathCollapse", new CollapsableRewriteEdgesProvider(EdgeType.REWRITE), new NodeCollapsingPathGenerator(), maxEdgeGain);
    }

}
