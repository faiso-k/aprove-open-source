package aprove.verification.oldframework.Bytecode.Processors.ToComplexity;

import java.util.Optional;

import aprove.Globals;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * available Terms are:
 * this (referes to the the 0th local variable for non static methods)
 * ret (the returned value)
 * env (the environment, used i.e. for reading/writing files)
 * argi (the i-th argument of the method, starting at 0)
 *
 */
public interface ComplexityGoalTerm {
    
    String getStringRepresentation();
    Optional<AbstractVariableReference> getReferenceFromStackFrame(StackFrame stackFrame);
    default Optional<TRSTerm> getTerm() {
        return Optional.empty();
    }
    
    static ComplexityGoalTerm valueOf(String s) {
        return fromString(s).get();
    }
    
    static Optional<ComplexityGoalTerm> fromString(String s) {
        switch(s) {
        case "this":
            return Optional.of(ComplexityGoalTerm.THIS);
        case "ret":
            return Optional.of(ComplexityGoalTerm.RET);
        case "env":
            return Optional.of(ComplexityGoalTerm.ENV);
        case "static":
            return Optional.of(ComplexityGoalTerm.STATIC);
        default:
            if (s.startsWith("arg")) {
                try {
                    int i = Integer.parseInt(s.substring(3));
                    return Optional.of(ComplexityGoalTerm.arg(i));
                } catch (NumberFormatException e) {
                    return Optional.empty();
                }
            } else {
                return Optional.empty();
            }
        }
    }
    
    ComplexityGoalTerm THIS = new Arg(-1) {
        @Override
        public String getStringRepresentation() {
            return "this";
        }
    };
    
    ComplexityGoalTerm RET = new ComplexityGoalTerm() {
        
        @Override
        public String getStringRepresentation() {
            return "ret";
        }
        @Override
        public String toString() {
            return this.getStringRepresentation();
        }

        @Override
        public Optional<AbstractVariableReference> getReferenceFromStackFrame(StackFrame stackFrame) {
            if (Globals.useAssertions) {
                assert stackFrame.getCurrentOpCode() instanceof Return;
            }
            return Optional.of(stackFrame.peekOperandStack(0)); //the return value should be on top of the operand stack
        }
    };
    
    ComplexityGoalTerm ENV = new ComplexityGoalTerm() {
        @Override
        public String getStringRepresentation() {
            return "env";
        }
        @Override
        public String toString() {
            return this.getStringRepresentation();
        }
        
        @Override
        public Optional<AbstractVariableReference> getReferenceFromStackFrame(StackFrame stackFrame) {
            return Optional.empty();
        }

        @Override
        public Optional<TRSTerm> getTerm() {
            return Optional.of(JBCGraphEdgesToIntTrsProcessor.ENV);
        }
    };

    ComplexityGoalTerm STATIC = new ComplexityGoalTerm() {
        @Override
        public String getStringRepresentation() {
            return "static";
        }
        @Override
        public String toString() {
            return this.getStringRepresentation();
        }

        @Override
        public Optional<AbstractVariableReference> getReferenceFromStackFrame(StackFrame stackFrame) {
            return Optional.empty();
        }

        @Override
        public Optional<TRSTerm> getTerm() {
            return Optional.of(JBCGraphEdgesToIntTrsProcessor.STATIC);
        }
    };

    public static Arg arg(int i) {
        assert i>=0;
        return new Arg(i);
    }
    
    class Arg implements ComplexityGoalTerm {
        private final int index;
        
        private Arg(int i) {
            this.index = i;
        }

        public int getI() {
            return index;
        }

        @Override
        public String getStringRepresentation() {
            return "arg" + index;
        }
        @Override
        public String toString() {
            return this.getStringRepresentation();
        }

        @Override
        public Optional<AbstractVariableReference> getReferenceFromStackFrame(StackFrame stackFrame) {
            int i = index;
            if (!stackFrame.getMethod().isStatic()) i++; //account for "this"
            return Optional.of(stackFrame.getInputReferences().getRootInputReference(LocVarRootPosition.create(0, i)).getReference());
        }
    }
}
