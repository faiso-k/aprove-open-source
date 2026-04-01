package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.Collection;
import java.util.Map;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Filter that rejects edges where classes are loaded, ignores Noop-Initializations.
 * Is implemented as singleton because there are no fields needed.
 * @author tys
 */
public class NoClassLoadingEdgeFilter implements EdgeFilter {

    //no need to create more then one instance
    private NoClassLoadingEdgeFilter() {};
    public static final NoClassLoadingEdgeFilter INSTANCE = new NoClassLoadingEdgeFilter();

    @Override
    public boolean selectEdge(Node from, Node to, EdgeInformation e) {
        if (e instanceof InitializationStateChange) {
            State s = from.getState();
            ClassPath cPath = s.getClassPath();
            Map<ClassName, InitStatus> initStatus = from.getState().getClassInitInfo().getClassesWithInitializationState(s.getJBCOptions());

            Collection<Triple<ClassName, InitStatus, InitStatus>> infos = ((InitializationStateChange) e).getNewInitStates();
            for (Triple<ClassName, InitStatus, InitStatus> info : infos) {
                if (!ObjectRefinement.hasNoopInit(cPath.getClass(info.x), initStatus)) {
                    return false; //something was initialized
                }
            }
        }
        return true;
    }
}