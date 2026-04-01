package aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.PathGenerators;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Processors.GraphProcessors.EdgeCollapse.EdgeProviders.*;

/**
 *
 * @author MP
 */
public interface CollapsablePathGenerator {

    public CollapsedPathsResult collapsePaths(final TIDPProblem idp,
        final CollapsableEdgesProvider collapsableProvider,
        final float maxEdgeGain,
        final Abortion aborter) throws AbortionException;

    public String getName();

}
