package aprove.verification.oldframework.Bytecode.OpCodes;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Represent the instanceof and checkcast opcodes.
 * @author Christian von Essen, Marc Brockschmidt
 */
public class CheckCast extends OpCode {
    /**
     * Enumeration of known behaviors when performing a cast check.
     */
    public enum CastCheckType {
        /**
         * The cast check should behave like the instanceof opcode (object
         * reference on the stack is replaced by an integer indicating the
         * result, result is 0 for the null pointer).
         */
        INSTANCEOF,

        /**
         * The cast check should behave like the checkcast opcode (object
         * reference stays on the stack, all non-fitting types result in an
         * exception, the null pointer is considered to be fitting).
         */
        CHECKCAST
    }

    /**
     * Stores the fully qualified name of the class against which objects are
     * checked.
     */
    private final FuzzyType checkedType;

    /**
     * Type of the cast check to be performed.
     */
    private final CastCheckType castCheckType;

    /**
     * @param checkedT Fully qualified name of the type which the checked object
     * should have.
     * @param checkType Type of the cast check to be performed.
     */
    public CheckCast(final FuzzyType checkedT, final CastCheckType checkType) {
        if (Globals.useAssertions) {
            /*
             * checkedT is the type that is the target of the check, which is
             * loaded from the constant pool and cannot be abstract.
             */
            assert (!(checkedT instanceof FuzzyPrimitiveType && !checkedT.isArrayType())) : "Check cast to primitive type "
                + checkedT
                + " is not supported";
            assert (!(checkedT instanceof FuzzyClassType) || checkedT.isConcrete()) : "Check cast to abstract type "
                + checkedT
                + " is not supported";
        }
        this.checkedType = checkedT;
        this.castCheckType = checkType;
    }

    /**
     * @return String representation of this branch opcode
     */
    @Override
    public String toString() {
        return this.castCheckType + " " + this.checkedType;
    }

    /**
     * Generates a number of new states from a current state, either by checking
     * the type, or if that isn't possible, specializing the type of the checked
     * object enough to allow a decision.
     * @param s The old state
     * @param out add the refined states and the connecting edges here
     * @return a number of successor states created by either evaluation,
     * refinement or splitting.
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        final StackFrame curFrame = s.getCurrentStackFrame();
        final AbstractVariableReference oR = curFrame.peekOperandStack(0);

        // We need to know if the instance to compare with is null
        if (ObjectRefinement.forExistence(oR, s, out)) {
            return true;
        }

        if (oR.isNULLRef()) {
            return false;
        }

        boolean isJlo = s.getAbstractType(oR).isAbstractJLOLike();
        boolean forceSplit = s.getJBCOptions().avoidExpandingTypeTree() && isJlo;
        if (forceSplit) {
            if (s.getSplitResult() == null) {
                State trueState = s.clone();
                trueState.setSplitResult(new BooleanSplitResult(true));
                State falseState = s.clone();
                falseState.setSplitResult(new BooleanSplitResult(false));
                out.add(new Pair<>(trueState, new SplitEdge(Collections.singleton(trueState.getCurrentStackFrame().peekOperandStack(0)))));
                out.add(new Pair<>(falseState, new SplitEdge(Collections.singleton(falseState.getCurrentStackFrame().peekOperandStack(0)))));
                return true;
            }
        } else if (ObjectRefinement.forTypeOfInterest(oR, this.checkedType, false, s, out)) {
            return true;
        }

        /*
         * CHECKCAST may throw a ClassCastException, so we may need to
         * initialize it.
         */
        if (this.castCheckType == CastCheckType.CHECKCAST) {
            final AbstractType subjectS = s.getAbstractType(oR);
            final Boolean assignmentCompatible = subjectS.isAssignmentCompatibleTo(this.checkedType, s.getClassPath());

            // we should be able to decide this after typeOfInterest refinement
            assert (assignmentCompatible != null);
            boolean needsClassCastException;
            if (forceSplit) {
                needsClassCastException = !((BooleanSplitResult) s.getSplitResult()).getTruthValue();
            } else {
                needsClassCastException = !assignmentCompatible.booleanValue();
            }
            if (needsClassCastException && ObjectRefinement.forInitialization(Important.CLASSCAST_EXC, s, out)) {
                return true;
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final Pair<State, EdgeInformation> evaluate(final State curState) {
        final State newState = curState.clone();
        final EdgeInformation edge;
        final StackFrame curFrame = newState.getCurrentStackFrame();
        final AbstractVariableReference oR = curFrame.peekOperandStack(0);
        final AbstractType subjectS = newState.getAbstractType(oR);

        if (curState.getSplitResult() == null) {
            if (this.castCheckType == CastCheckType.CHECKCAST) {
                // NULL is always OK
                if (oR.isNULLRef() || subjectS.isAssignmentCompatibleTo(this.checkedType, curState.getClassPath())) {
                    curFrame.setCurrentOpCode(this.getNextOp());
                    edge = new EvaluationEdge();
                } else {
                    edge = new MethodStartEdge();
                    throwException(newState, CLASSCAST_EXC);
                }
            } else if (this.castCheckType == CastCheckType.INSTANCEOF) {
                edge = new EvaluationEdge();
                curFrame.popOperandStack();
                curFrame.setCurrentOpCode(this.getNextOp());

                // We need to know if the instance to compare with is null
                // null instanceof Object == false
                if (!oR.isNULLRef() && subjectS.isAssignmentCompatibleTo(this.checkedType, curState.getClassPath())) {
                    final AbstractVariableReference newVarRef =
                            newState.createReferenceAndAdd(AbstractInt.getOne(), OperandType.INTEGER);
                    curFrame.pushOperandStack(newVarRef);
                } else {
                    final AbstractVariableReference newVarRef =
                            newState.createReferenceAndAdd(AbstractInt.getZero(), OperandType.INTEGER);
                    curFrame.pushOperandStack(newVarRef);
                }
            } else {
                assert false;
                return null;
            }
        } else {
            if (oR.isNULLRef()) {
                edge = new EvaluationEdge();
                if (this.castCheckType == CastCheckType.INSTANCEOF) {
                    AbstractVariableReference newRef = newState.createReferenceAndAdd(AbstractInt.getOne(), OperandType.INTEGER);
                    newState.getCurrentStackFrame().popOperandStack();
                    newState.getCurrentStackFrame().pushOperandStack(newRef);
                }
                newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
            } else {
                boolean b = ((BooleanSplitResult) curState.getSplitResult()).getTruthValue();
                if (b) {
                    FuzzyType resultingType;
                    if (checkedType instanceof FuzzyClassType) {
                        resultingType = ((FuzzyClassType) checkedType).toAbstract();
                    } else {
                        resultingType = checkedType;
                    }
                    newState.setAbstractType(oR, new AbstractType(curState.getClassPath(), resultingType));
                    edge = new EvaluationEdge();
                    if (this.castCheckType == CastCheckType.INSTANCEOF) {
                        AbstractVariableReference newRef = newState.createReferenceAndAdd(AbstractInt.getOne(), OperandType.INTEGER);
                        newState.getCurrentStackFrame().popOperandStack();
                        newState.getCurrentStackFrame().pushOperandStack(newRef);
                    }
                    newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
                } else {
                    if (this.castCheckType == CastCheckType.CHECKCAST) {
                        edge = new MethodStartEdge();
                        throwException(newState, CLASSCAST_EXC);
                    } else if (this.castCheckType == CastCheckType.INSTANCEOF) {
                        edge = new EvaluationEdge();
                        AbstractVariableReference newRef = newState.createReferenceAndAdd(AbstractInt.getZero(), OperandType.INTEGER);
                        newState.getCurrentStackFrame().popOperandStack();
                        newState.getCurrentStackFrame().pushOperandStack(newRef);
                        newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
                    } else {
                        throw new RuntimeException();
                    }
                }
            }
        }
        return new Pair<>(newState, edge);
    }

    @Override
    public int getNumberOfArguments() {
        return 1;
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
