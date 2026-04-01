package aprove.verification.oldframework.Bytecode.Natives;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of the getPrimitiveClass(LString;) method in java.lang.Class.
 * Returns a class object for the primitive type specified in the argument
 * string, or throws an exception if the string describes an unknown type.
 *
 * @author Marc Brockschmidt
 */
public class GetPrimitiveClass extends PredefinedMethod {
    /** { @inheritDoc } */
    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(final State s) {
        //Get the argument:
        final AbstractVariableReference stringRef = s.getCallStack().getTop().getOperandStack().peek(0);

        //Prepare the new state
        final State newState = s.clone();

        //Handle the null pointer case
        if (stringRef.isNULLRef()) {
            OpCode.throwException(newState, NPE_EXC);
            return new Pair<>(newState, new MethodStartEdge());
        }

        final String referencedClassName = s.getConcreteString(stringRef);

        final FuzzyPrimitiveType chosenTypeClass;

        //Yay, we could decide:
        if (referencedClassName != null) {
            if (referencedClassName.equals("boolean")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.BOOLEAN, 0);
            } else if (referencedClassName.equals("char")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.CHAR, 0);
            } else if (referencedClassName.equals("float")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.FLOAT, 0);
            } else if (referencedClassName.equals("double")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.DOUBLE, 0);
            } else if (referencedClassName.equals("byte")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.BYTE, 0);
            } else if (referencedClassName.equals("short")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.SHORT, 0);
            } else if (referencedClassName.equals("int")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.INTEGER, 0);
            } else if (referencedClassName.equals("long")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.LONG, 0);
            } else if (referencedClassName.equals("void")) {
                chosenTypeClass = new FuzzyPrimitiveType(OperandType.VOID, 0);
            } else {
                chosenTypeClass = null;
            }
        } else {
            //Get the split result:
            final GetPrimitiveClassSplitResult splitRes = (GetPrimitiveClassSplitResult) s.getSplitResult();

            chosenTypeClass = splitRes.getChosenPrimType();
        }

        EdgeInformation edge;
        //Prepare the new state, get the fitting class:
        if (chosenTypeClass != null) {
            newState.getCallStack().getTop().getOperandStack().pop();
            final AbstractVariableReference ref =
                JLClassHelper.addConstantClassToStateOrThrow(newState, chosenTypeClass);
            newState.getCurrentStackFrame().setCurrentOpCode(s.getCurrentOpCode().getNextOp());
            newState.getCurrentStackFrame().getOperandStack().push(ref);
            edge = new EvaluationEdge();
        } else {
            OpCode.throwException(newState, Important.CLASSNOTFOUND_EXC);
            edge = new MethodStartEdge();
        }
        return new Pair<State, EdgeInformation>(newState, edge);
    }

    /** { @inheritDoc } */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        //We had a split already:
        if (s.getSplitResult() != null) {
            return false;
        }

        final AbstractVariableReference stringRef = s.getCurrentStackFrame().peekOperandStack(0);

        // make sure we are not dealing with null
        if (ObjectRefinement.forExistence(stringRef, s, result)) {
            return true;
        }

        if (stringRef.isNULLRef()) {
            return false;
        }

        if (ObjectRefinement.forRealization(
            stringRef,
            s.getClassPath().getTypeTree(ClassName.Important.JAVA_LANG_STRING.getClassName()),
            null,
            s,
            result,
            true))
        {
            return true;
        }

        if (ObjectRefinement.forEquality(stringRef, s, result)) {
            return true;
        }

        final String referencedClassName = s.getConcreteString(stringRef);
        //Yay, we can decide:
        if (referencedClassName != null) {
            return false;
        }

        /*
         * We must guess which primitive type this is. Don't forget the
         * possibility that we are handling a null pointer (we can decide
         * this!) We have to handle "boolean", "char", "float", "double",
         * "byte", "short", "int", "long" and "void". In no case,
         * getPrimitiveClass is called with a non-matching argument, so
         * we don't need to split for the ClassNotFoundError possibility:
         *
         * JNIEXPORT jclass JNICALL
         * Java_java_lang_Class_getPrimitiveClass(JNIEnv *env,
         *                      jclass cls,
         *                      jstring name)
         * {
         *   const char *utfName;
         *   jclass result;
         *
         *   if (name == NULL) {
         *   JNU_ThrowNullPointerException(env, 0);
         *   return NULL;
         *   }
         *
         *   utfName = (*env)->GetStringUTFChars(env, name, 0);
         *   if (utfName == 0)
         *       return NULL;
         *
         *   result = JVM_FindPrimitiveClass(env, utfName);
         *
         *    (*env)->ReleaseStringUTFChars(env, name, utfName);
         *
         *   return result;
         * }
         * [ java6/j2se/src/share/native/java/lang/Class.c ]
         *
         * JVM_ENTRY(jclass, JVM_FindPrimitiveClass(JNIEnv* env, const char* utf))
         *   JVMWrapper("JVM_FindPrimitiveClass");
         *   oop mirror = NULL;
         *   BasicType t = name2type(utf);
         *   if (t != T_ILLEGAL && t != T_OBJECT && t != T_ARRAY) {
         *    mirror = Universe::java_mirror(t);
         *   }
         *   if (mirror == NULL) {
         *    THROW_MSG_0(vmSymbols::java_lang_ClassNotFoundException(), (char*) utf);
         *   } else {
         *    return (jclass) JNIHandles::make_local(env, mirror);
         *   }
         * JVM_END
         * [ java6/hotspot/src/share/vm/prims/jvm.cpp ]
         *
         * BasicType name2type(const char* name) {
         *  for (int i = T_BOOLEAN; i <= T_VOID; i++) {
         *   BasicType t = (BasicType)i;
         *   if (type2name_tab[t] != NULL && 0 == strcmp(type2name_tab[t], name))
         *    return t;
         *  }
         *  return T_ILLEGAL;
         * }
         * [ java6/hotspot/src/share/vm/utilities/globalDefinitions.cpp ]
         */
        final AbstractVariableReference nameRef = s.getCallStack().getTop().getOperandStack().peek(0);

        //Ensure that the string actually exists:
        if (ObjectRefinement.forExistence(nameRef, s, result)) {
            return true;
        }

        //If it doesn't exist, prepare the null ref:
        if (nameRef.isNULLRef()) {
            if (ObjectRefinement.forInitialization(NPE_EXC, s, result)) {
                return true;
            }
        }

        //Now just split. Create a state for each possible result:
        final FuzzyPrimitiveType[] possiblePrimitiveTypes =
            new FuzzyPrimitiveType[] {
                new FuzzyPrimitiveType(OperandType.BOOLEAN, 0),
                new FuzzyPrimitiveType(OperandType.CHAR, 0),
                new FuzzyPrimitiveType(OperandType.FLOAT, 0),
                new FuzzyPrimitiveType(OperandType.DOUBLE, 0),
                new FuzzyPrimitiveType(OperandType.BYTE, 0),
                new FuzzyPrimitiveType(OperandType.SHORT, 0),
                new FuzzyPrimitiveType(OperandType.INTEGER, 0),
                new FuzzyPrimitiveType(OperandType.LONG, 0),
                new FuzzyPrimitiveType(OperandType.VOID, 0),
                null };

        for (final FuzzyPrimitiveType chosenType : possiblePrimitiveTypes) {
            final State newState = s.clone();
            newState.setSplitResult(new GetPrimitiveClassSplitResult(chosenType));
            result.add(new Pair<State, EdgeInformation>(newState, new SplitEdge(Collections.singleton(stringRef))));
        }

        return true;
    }

}
