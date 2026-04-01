package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Represent creation of new object instances.
 *
 * @author Christian von Essen, Marc Brockschmidt
 */
public class New extends OpCode {
    /**
     * Name of the class of which an instance should be created.
     */
    private final ClassName className;

    /**
     * @param classN parsed class name of the instance to create.
     */
    public New(final ClassName classN) {
        assert (classN != null);
        this.className = classN;
    }

    /**
     * @return String representation of this {@link New} opcode.
     */
    @Override
    public String toString() {
        return "New " + this.className;
    }

    /**
     * Generates exactly one new state from the current state by performing the
     * object creation represented by this instance.
     *
     * @param state The old state
     * @return a list with exact one successor states created by this operation.
     */
    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(final State state) {
        final State newState = state.clone();

        final IClass parsedClass =
            Resolver.resolveClassOrThrow(state.getClassPath(), this.className, newState, this
                .getMethod()
                .getIClass()
                .getType());

        if (parsedClass == null) {
            return new Pair<>(newState, new MethodStartEdge());
        } else {
            final AbstractVariableReference newRef = New.fillState(newState, parsedClass);
            newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
            final EvaluationEdge evalEdge = new EvaluationEdge();
            evalEdge.add(new ObjectCreationInformation(newRef, this.className));
            return new Pair<>(newState, evalEdge);
        }
    }

    /** {@inheritDoc} */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        // Try to load the class; if we can't find it, there is no need to refine any further
        final IClass parsedClass = Resolver.resolveClass(s.getClassPath(), this.className, this);
        if (parsedClass == null) {
            return ObjectRefinement.forInitialization(ClassName.Important.CLASSNOTFOUND_EXC, s, out);
        }

        return ObjectRefinement.forInitialization(parsedClass, s, out);
    }

    /**
     * Create a new instance, fill the state with corresponding information and
     * push the reference onto the operand stack.
     * @param newState the state to work with
     * @param parsedClass the class of the instance to create
     * @return reference to newly created (empty) object
     */
    public static AbstractVariableReference fillState(final State newState, final IClass parsedClass) {
        final TypeTree typeTree = parsedClass.getType();
        assert (typeTree != null) : "Couldn't get type tree for class " + parsedClass.getClassName();
        final ObjectInstance oI = ConcreteInstance.newInstanceFromType(newState, typeTree, FieldValueSettings.DEFAULT_VALUE);
        final AbstractVariableReference ref = newState.createReferenceAndAdd(oI, OperandType.ADDRESS);

        newState.getCurrentStackFrame().pushOperandStack(ref);
        newState.getHeapAnnotations().setAbstractType(
            ref,
            new AbstractType(newState.getClassPath(), new FuzzyClassType(typeTree.getClassName(), true)));
        newState.getHeapAnnotations().setReachableTypes(
            ref,
            new AbstractType(newState.getClassPath(), FuzzyClassType.FT_JAVA_LANG_OBJECT));

        return ref;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final State preEvalInst = postEvalInst.clone();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();

        /*
         * Just drop the newly created object ref:
         */
        curInstFrame.popOperandStack();
        curInstFrame.setCurrentOpCode(preEval.getCurrentOpCode());

        this.handleActiveVarChangesInRevEv(preEval, preEvalInst, postEval, refMap);

        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        return 0;
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
