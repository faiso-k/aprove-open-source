package aprove.verification.oldframework.Bytecode.Natives;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class SystemExit extends PredefinedMethod {

    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(State s) {
        return new Pair<>(new State(s.getClassPath(), s.getTerminationGraph()), new EvaluationEdge());
    }

}
