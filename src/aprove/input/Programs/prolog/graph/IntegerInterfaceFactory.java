package aprove.input.Programs.prolog.graph;

import java.util.*;

import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.constants.*;
import aprove.verification.oldframework.IntegerReasoning.equalSides.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;

/**
 * A simple factory to create an empty integer interface. Right now, a new instance of this is created and discarded
 * every time we need a new arithmetic state during the graph construction. The goal is to inject a single instance of
 * this factory where ever we need it instead.
 * @author Alexander Weinert
 */
public class IntegerInterfaceFactory {

    IntegerState createEmpty() {
        final List<IntegerState> backingInterfaces = new LinkedList<IntegerState>();
        backingInterfaces.add(new EqualSidesInterface());
        backingInterfaces.add(new ConstantInterface());
        backingInterfaces.add(new SmtIntegerState(new Z3ExtSolverFactory()));
        return CompositeIntegerInterface.build(backingInterfaces);
    }

}
