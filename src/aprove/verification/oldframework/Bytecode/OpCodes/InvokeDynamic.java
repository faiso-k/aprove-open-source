package aprove.verification.oldframework.Bytecode.OpCodes;

import static java.lang.invoke.MethodHandleInfo.*;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCodes.InvokeMethod.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.ConcreteInstance.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Essentially, InvokeDynamic executes arbitrary user-defined code to create an object which implements a certain
 * functional interface. Here, the "user" is typically the developer of the compiler that emits Java Bytecode.
 * For all occurrences of InvokeDynamic in the Bytecode emitted by javac, this user-defined method is
 * {@link java.lang.invoke.LambdaMetafactory#metafactory}. It dynamically creates a class which implements the required
 * functional interface. Clearly, there's no hope to handle InvokeDynamic in its full generality. Hence, this class
 * mocks the behavior of {@link java.lang.invoke.LambdaMetafactory#metafactory}.
 *
 * In the following, "the abstract method" refers to the unique abstract method in the implemented functional interface.
 *
 * TODO There are all kinds of implicit conversions going on all over the place -- we currently ignore them.
 * TODO There's crazy stuff happening with varargs-lambdas / references to varargs-methods -- we ignore these.
 */
public class InvokeDynamic extends OpCode {

    private MethodIdentifier idOfLambdaImpl;

    private ClassName functionalInterfaceName;

    /**
     * The closure of the lambda, i.e., variables which can be accessed by the lambda without being among its arguments
     * since they exist in the same scope. These variables have to be passed to {@link InvokeDynamic#idOfLambdaImpl}
     * explicitly, such that the implementation of the lambda can access them. However, they are not in the argument
     * list of the abstract function of the abstract method. Hence, they are stored in fields of the dynamically created
     * class and passed to {@link InvokeDynamic#idOfLambdaImpl} by the implementation of the abstract method.
     *
     * Note: {@link InvokeDynamic#capturedArgumentTypes} does NOT contain the type of the implicit first argument "this"
     *       if InvokeDynamic isn't used to resolve a lambda, but to resolve a reference to an instance method. Hence,
     *       this case has to be handled separately in {@link InvokeDynamic#evaluate}.
     */
    private List<FuzzyType> capturedArgumentTypes;

    private InvocationType invocationType;

    public InvokeDynamic(MethodIdentifier idOfLambdaImpl, ClassName functionalInterfaceName, int invocationType, List<FuzzyType> capturedArgumentTypes) {
        assert Arrays.asList(REF_invokeInterface, REF_invokeStatic, REF_invokeVirtual, REF_invokeSpecial, REF_newInvokeSpecial).contains(invocationType);
        this.idOfLambdaImpl = idOfLambdaImpl;
        this.functionalInterfaceName = functionalInterfaceName;
        this.capturedArgumentTypes = capturedArgumentTypes;
        this.invocationType = InvocationType.fromInt(invocationType);
    }

    @Override
    public String toString() {
        return "InvokeDynamic " + idOfLambdaImpl.getMethodName() + " " + functionalInterfaceName.getClassName();
    }

    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        if (ObjectRefinement.forInitialization(Important.JAVA_LANG_OBJECT, s, result)) {
            return true;
        }
        ClassPath cPath = s.getClassPath();
        IClass functionalInterface = cPath.getClass(functionalInterfaceName);
        if (ObjectRefinement.forInitialization(functionalInterface, s, result)) {
            return true;
        }
        return false;
    }

    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(State s) throws AbortionException {
        State newS = s.clone();
        ClassPath cPath = newS.getClassPath();
        IClass classOfLambdaImpl = cPath.getClass(idOfLambdaImpl.getClassName());
        IMethod lambdaImpl = classOfLambdaImpl.getLocalMethod(idOfLambdaImpl);
        IClass functionalInterface = cPath.getClass(functionalInterfaceName);
        IClass callingClass = newS.getCurrentStackFrame().getMethod().getIClass();
        DynamicClass dc = new DynamicClass(callingClass, functionalInterface, capturedArgumentTypes, lambdaImpl, invocationType);
        cPath.addClass(dc);
        newS.getClassInitInfo().setInitialized(dc.getClassName(), InitStatus.YES);
        // lambdaImpl is private, but InnerClassLambdaMetafactory#buildCallSite makes it accessible via reflection
        // here, we mimic this behavior
        lambdaImpl.setAccessible(dc.getClassName());
        ConcreteInstance var = ConcreteInstance.newInstanceFromType(newS, dc.getType(), FieldValueSettings.DEFAULT_VALUE);
        AbstractVariableReference ref = AbstractVariableReference.create(var, OperandType.ADDRESS);
        newS.addAbstractVariable(ref, var);
        AbstractType type = new AbstractType(cPath, new FuzzyClassType(dc.getClassName(), true));
        newS.setAbstractType(ref, type);
        newS.getHeapAnnotations().setReachableTypes(ref, type);
        Set<DefiniteReachabilityAnnotationCreation> newDefReach = new LinkedHashSet<>();
        OperandStack opStack = newS.getCurrentStackFrame().getOperandStack();
        // write the closure (i.e., the captured arguments) to the fields of the fresh instance
        // the names of these fields are arg$i, see constructor of InnerClassLambdaMetafactory
        // if we don't deal with a lambda, but with a reference to an instance method, then "this" is also captured
        Stack<AbstractVariableReference> toWrite = new Stack<>();
        // peek instead of push and...
        for (int i = 0; i < capturedArgumentTypes.size(); i++) {
            toWrite.push(opStack.peek(i));
        }
        // push the reference to the fresh object to make sure that all affected references have state positions when
        // putField is evaluated -- otherwise, putField fails with an assertion error
        opStack.push(ref);
        for (int i = 0; i < toWrite.size(); i++) {
            newDefReach.addAll(var.putField(newS, ref, dc.getClassName(), getArgName(i), toWrite.pop()));
        }
        // pop the reference to the fresh object...
        opStack.pop();
        // ...pop all references that have been consumed by this opcode...
        for (int i = 0; i < capturedArgumentTypes.size(); i++) {
            opStack.pop();
        }
        // ...and finally push the reference to the fresh object again
        opStack.push(ref);
        EvaluationEdge edge = new EvaluationEdge();
        edge.addAll(newDefReach);
        newS.setCurrentOpCode(newS.getCurrentOpCode().getNextOp());
        return new Pair<>(newS, edge);
    }

    public static String getArgName(int i) {
        return "arg$" + i;
    }

    @Override
    public int getNumberOfArguments() {
        return capturedArgumentTypes.size();
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
