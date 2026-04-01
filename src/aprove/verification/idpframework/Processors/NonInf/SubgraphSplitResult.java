package aprove.verification.idpframework.Processors.NonInf;

import java.util.*;

import aprove.verification.idpframework.Core.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class SubgraphSplitResult {

    private final ImmutableSet<IDPSubGraph> newSubGraphs;
    private final ImmutableSet<IDPProblem> newIDPProblems;

    public SubgraphSplitResult(final ImmutableSet<IDPSubGraph> newSubGraphs, final ImmutableSet<IDPProblem> newIDPProblems) {
        this.newSubGraphs = newSubGraphs;
        this.newIDPProblems = newIDPProblems;
    }

    public Set<IDPSubGraph> getNewSubGraphs() {
        return this.newSubGraphs;
    }

    public Set<IDPProblem> getNewIDPProblems() {
        return this.newIDPProblems;
    }

}
