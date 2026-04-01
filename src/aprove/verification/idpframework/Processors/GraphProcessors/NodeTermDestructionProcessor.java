package aprove.verification.idpframework.Processors.GraphProcessors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class NodeTermDestructionProcessor extends AbstractGraphProcessor<Result, TIDPProblem> {

    protected NodeTermDestructionProcessor() {
        super("NodeTermDestructionProcessor");
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    protected Result processIDPProblem(final TIDPProblem idp, final Abortion aborter)
            throws AbortionException {
        final IDependencyGraph graph = idp.getIdpGraph();

        final FreshNameGenerator freshNames = new FreshNameGenerator(graph.getFunctionSymbols(), FreshNameGenerator.FRIENDLYNAMES);
        final IDPPredefinedMap predefinedMap = graph.getPredefinedMap();

        final Map<INode, ITerm<?>> newNodeTerms = new LinkedHashMap<INode, ITerm<?>>();
        for (final Map.Entry<INode, ? extends ITerm<?>> nodeEntry : graph.getNodeMap().entrySet()) {
            if (nodeEntry.getValue().isVariable()) {
                newNodeTerms.put(nodeEntry.getKey(), nodeEntry.getValue());
            } else {
                final IFunctionApplication<?> nodeTerm = (IFunctionApplication<?>) nodeEntry.getValue();

                final Set<IVariable<?>> nodeVariables = nodeTerm.getVariables();
                final IFunctionSymbol<?> newFs = IFunctionSymbol.create(nodeTerm.getName(), nodeVariables.size(), predefinedMap);
                assert newFs.getSemantics() == null : "illegal match to predefined symbol";

                final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(nodeVariables);
                final IFunctionApplication<?> newNodeTerm = ITerm.createFunctionApplication(newFs, ImmutableCreator.create(newArgs));
            }
        }


        return null;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

}
