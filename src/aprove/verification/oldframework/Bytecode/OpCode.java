package aprove.verification.oldframework.Bytecode;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.math.*;
import java.util.*;

import org.json.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
  * Mother class of all opcodes.
  * @author Christian von Essen, Marc Brockschmidt
  */
public abstract class OpCode {
    /**
     * Convenience ENUM for often used operand types and their lengths in words.
     */
    public static enum OperandType {
        /**
         * Integer operands (length: one word == 4 byte)
         */
        INTEGER("INT", 1, 'I', IntegerType.I32) {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av instanceof AbstractInt);
            }
        },

        /**
         * Long integer operands (length: two words == 8 byte)
         */
        LONG("LONG", 2, 'J', IntegerType.I64) {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av instanceof AbstractInt);
            }
        },

        /**
         * Floating point number operands (length: one word == 4 byte)
         */
        FLOAT("FLOAT", 1, 'F', null) {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av instanceof AbstractFloat);
            }
        },

        /**
         * Floating point number (double precision) operands (length: two words == 8 byte)
         */
        DOUBLE("DOUBLE", 2, 'D', null) {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av instanceof AbstractFloat);
            }
        },

        /**
         * Reference/Pointer operands (length: one word == 4 byte)
         */
        ADDRESS("ADDR") {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av == null || av instanceof Array || av instanceof ObjectInstance);
            }
        },

        /**
         * Byte operands (length: one word == 4 byte)
         */
        BYTE("BYTE", 1, 'B', IntegerType.I8) {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av instanceof AbstractInt);
            }
        },

        /**
         * Char operands (length: one word == 4 byte)
         */
        CHAR("CHAR", 1, 'C', IntegerType.UI16) {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av instanceof AbstractInt);
            }
        },

        /**
         * Short operands (length: one word == 4 byte)
         */
        SHORT("SHORT", 1, 'S', IntegerType.I16) {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av instanceof AbstractInt);
            }
        },

        /**
         * Boolean operands (length: one word == 4 byte)
         */
        BOOLEAN("BOOL", 1, 'Z', IntegerType.I1) {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av instanceof AbstractInt);
            }
        },

        /**
         * Array (glorified reference) operands (length: one word == 4 byte)
         */
        ARRAY("ARRAY") {
            @Override
            public boolean check(final AbstractVariable av) {
                return (av == null || av instanceof Array || av instanceof ObjectInstance);
            }
        },

        /**
         * Return address (length: one word)
         */
        RETURN_ADDRESS("RET_ADDR") {
            @Override
            public boolean check(final AbstractVariable av) {
                return false;
            }
        },

        /**
         * Nothing. Never actually used, but needed from time to time
         * for formal reasons
         */
        VOID("VOID", 1, 'V', null) {
            @Override
            public boolean check(final AbstractVariable av) {
                return false;
            }
        };

        /**
         * Short name to be used for output.
         */
        private final String shortName;

        /**
         * True iff this represents a primitive type.
         */
        private final boolean isPrimitive;

        /**
         * Number of words used up by values of this operand type.
         */
        private final int words;

        /**
         * The character used in field descriptors (if this is a primitive
         * type).
         */
        private final char primChar;

        /**
         * The type of this integer value, giving lower and upper bounds (if applicable).
         */
        private final transient IntegerType integerType;

        /**
         * @param shortN short name to be used for output.
         */
        private OperandType(final String shortN) {
            this(shortN, 1, false, '\u0000', null);
        }

        /**
         * @param shortN short name to be used for output.
         * @param wordParam number of bytes
         * @param primCharArg the character used in field descriptors (if this
         * is a primitive type)
         * @param intType the type of this integer value, giving lower and upper bounds (if applicable).
         */
        private OperandType(final String shortN, final int wordParam, final char primCharArg, final IntegerType intType)
        {
            this(shortN, wordParam, true, primCharArg, intType);
        }

        /**
         * @param shortN short name to be used for output.
         * @param wordParam number of bytes
         * @param isPrimitiveParam true iff this represents a primitive type
         * @param primCharArg the character used in field descriptors (if this
         * is a primitive type)
         * @param intType the type of this integer value, giving lower and upper bounds (if applicable).
         */
        private OperandType(
            final String shortN,
            final int wordParam,
            final boolean isPrimitiveParam,
            final char primCharArg,
            final IntegerType intType)
        {
            this.shortName = shortN;
            this.words = wordParam;
            this.isPrimitive = isPrimitiveParam;
            this.primChar = primCharArg;
            this.integerType = intType;
        }

        /**
         * @return a nice string representation of this opcode
         */
        @Override
        public final String toString() {
            return this.shortName;
        }

        /**
         * @return number of words (== 4 bytes) used up by values of this type
         */
        public final int getWords() {
            return this.words;
        }

        /**
         * Check if the given variable has a type that matches this type.
         * @param av some abstract variable
         * @return true iff the types match
         */
        public abstract boolean check(final AbstractVariable av);

        /**
         * @return true iff this represents a primitive type
         */
        public boolean isPrimitive() {
            return this.isPrimitive;
        }

        /**
         * @return the character used to represent this type inside field
         * descriptors
         */
        public char getCharacter() {
            assert (this.isPrimitive);
            return this.primChar;
        }

        /**
         * @return the short name used to describe this type (i.e. "short" or
         *  "boolean");
         */
        public String getShortName() {
            assert (this.isPrimitive);
            if (this == OperandType.BOOLEAN) {
                // We called this "BOOL"...
                return "boolean";
            } else {
                return this.shortName.toLowerCase();
            }
        }

        /**
         * @param varRefName some variable reference name
         * @return the probable type of the referenced variable
         */
        public static OperandType guessOperandType(final String varRefName) {
            if (varRefName.startsWith("i")) {
                return OperandType.INTEGER;
            } else if (varRefName.startsWith("o")) {
                return OperandType.ADDRESS;
            } else if (varRefName.startsWith("a")) {
                return OperandType.ARRAY;
            } else {
                // Removed this assert as we actually might have an input which is no varRef.
                // assert (false) : "Can't guess operand type from var ref name "
                //       + varRefName;
                return null;
            }
        }

        /**
         * @param character a character defining an operand type
         * @return the operand type defined by the given character
         */
        public static OperandType fromCharacter(final char character) {
            for (final OperandType tryMe : OperandType.values()) {
                if (tryMe.primChar == character) {
                    return tryMe;
                }
            }
            throw new RuntimeException("Not a class type signature: " + character);
        }

        /**
         * @return the minimal value for this primitive type
         */
        public BigInteger getMinValue() {
            return this.integerType.getLower().getConstant();
        }

        /**
         * @return the maximum value for this primitive type
         */
        public BigInteger getMaxValue() {
            return this.integerType.getUpper().getConstant();
        }

        /**
         * @return the maximum value for this primitive type
         */
        public IntegerType getIntegerType() {
            return this.integerType;
        }

        public char getPrimChar() {
            return primChar;
        }
    }

    volatile private Map<OpCode, Integer> reachabilityCache = new HashMap<>();

    /**
     * Used to have some order over opcodes.
     */
    private static int opCodeCounter;

    /**
     * Used to have some order over opcodes.
     */
    private final int id;

    /**
     * Opcode following this one (usually the next one to be evaluated, iff no
     * branching/exception handling is needed)
     */
    private OpCode nextOp;

    /**
     * Opcode preceding this. Usually evaluated last.
     */
    private OpCode lastOp;

    /**
     * Position in the opcode array in the class file.
     */
    private int pos;

    /**
     * Method in which this opcode is used.
     */
    private IMethod method;

    /**
     * The exception table for this opcode (order is important!)
     */
    private final List<Pair<ClassName, OpCode>> exceptionTable;

    /**
     * Default constructor (preparing the exception table object)
     */
    public OpCode() {
        this.exceptionTable = new LinkedList<>();
        this.id = OpCode.opCodeCounter++;
    }

    /**
     * @param t OpCode following this opcode.
     */
    public void setNextOp(final OpCode t) {
        this.nextOp = t;
    }

    /**
     * @return OpCode following this opcode.
     */
    public OpCode getNextOp() {
        return this.nextOp;
    }

    /**
     * @return OpCode preceding this opcode.
     */
    public OpCode getLastOp() {
        return this.lastOp;
    }

    /**
     * @param l OpCode preceding this opcode.
     */
    public void setLastOp(final OpCode l) {
        this.lastOp = l;
    }

    /**
     * @return Position in the bytecode array of this method.
     */
    public int getPos() {
        return this.pos;
    }

    /**
     * @param p in the bytecode array of this method.
     */
    public void setPos(final int p) {
        this.pos = p;
    }

    /**
     * @return method in which this opcode is used.
     */
    public IMethod getMethod() {
        return this.method;
    }

    /**
     * @param m method in which this opcode is used.
     */
    public void setMethod(final IMethod m) {
        this.method = m;
    }

    /**
     * @return the short name for this OpCode, for use in the TRS encoding of
     *  the symbolic evaluation.
     */
    public String getShortName() {
        return this.getClass().getSimpleName();
    }

    /**
     * @param detail if false, the string output should be short
     * @return a wonderful string representation
     */
    public String toString(final boolean detail) {
        return this.toString();
    }

    /**
     * @param exceptionClass the exception class handled by handlerOpCode
     * @param handlerOpCode the beginning of the handler for exceptions of type exceptionClass
     */
    public void addExceptionHandler(final ClassName exceptionClass, final OpCode handlerOpCode) {
        this.exceptionTable.add(new Pair<>(exceptionClass, handlerOpCode));
    }

    /**
     * @param s Input state
     * @param result Object used for collecting the result
     * @return true if refinement was needed and done, false if no refinement was needed
     */
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        return false;
    }

    /**
     * @param s Input state
     * @return State and information of the result of the opcode's operation on the input state
     *
     * INVARIANT: May only be called, if @see refinment returns false for the same input state
     *            (i.e., only if no refinement is needed)
     * @throws AbortionException if this method is aborted
     */
    public abstract Pair<State, ? extends EdgeInformation> evaluate(final State s) throws AbortionException;

    /**
     * @return the exception table
     */
    public List<Pair<ClassName, OpCode>> getExceptionTable() {
        return this.exceptionTable;
    }

    /**
     * Take care that the thrown exception is handled.
     * @param origState the current state where the exception was thrown
     * @param newStates collection used for collecting the resulting states
     */
    public static final void handleException(
        final State origState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {
        final AbstractVariableReference exceptionRef = origState.getCurrentStackFrame().getException();
        assert (exceptionRef.pointsToInstance());
        // We need to know if the instance exists
        if (ObjectRefinement.forExistence(exceptionRef, origState, newStates)) {
            return;
        }

        final State state = origState.clone();
        final ObjectInstance o = (ObjectInstance) state.getAbstractVariable(exceptionRef);

        final List<FuzzyType> handledTypes = new LinkedList<>();
        for (final Pair<ClassName, OpCode> p : state.getCurrentOpCode().getExceptionTable()) {
            final ClassName classN = p.x;
            handledTypes.add((new FuzzyClassType(classN, true)));
        }

        if (ObjectRefinement.forTypesOfInterest(exceptionRef, handledTypes, true, origState, newStates)) {
            return;
        }

        if (o.isNULL()) {
            if (ObjectRefinement.forInitialization(NPE_EXC, state, newStates)) {
                return;
            }
            state.getCurrentStackFrame().unsetException();
            OpCode.throwException(state, NPE_EXC);
            newStates.add(new Pair<State, EdgeInformation>(state, new MethodStartEdge()));
            return;
        }

        final AbstractType type = origState.getAbstractType(exceptionRef);

        OpCode exceptionHandler = null;
        final StackFrame frame = state.getCurrentStackFrame();
        final OpCode opcode = frame.getCurrentOpCode();

        for (final Pair<ClassName, OpCode> entry : opcode.getExceptionTable()) {
            final ClassName classNameInTable = entry.x;
            /*
             * We know that the handler (exceptionInTable) always is a class,
             * not some interface.
             */

            /*
             * isAssignmentCompatibleTo does not return null, because we already
             * refined the type.
             */
            if (type.isAssignmentCompatibleTo(new FuzzyClassType(classNameInTable, true), origState.getClassPath())) {
                // We found it!
                exceptionHandler = entry.y;
                frame.setCurrentOpCode(exceptionHandler);
                assert (frame.getOperandStack().getStack().isEmpty());
                frame.pushOperandStack(exceptionRef);
                frame.unsetException();
                newStates.add(new Pair<State, EdgeInformation>(state, new CaughtExceptionEdge()));
                return;
            }
        }
        /*
         * Sadly, we did not find the exception handler. Now we have to drop the
         * frame and continue handling the exception below.
         */
        state.getCallStack().pop();
        if (!state.callStackEmpty()) {
            state.getCurrentStackFrame().setException(exceptionRef);

            // clear operand stack
            state.getCurrentStackFrame().getOperandStack().getStack().clear();
        }
        newStates.add(new Pair<State, EdgeInformation>(state, new UncaughtExceptionEdge()));
        return;
    }

    /**
     * Throw the given exception.
     * @param state the state that should be modified
     * @param exception an enum giving information about the class of the
     * exception
     */
    public static void throwException(final State state, final Important exception) {
        final IClass exceptionClass = state.getClassPath().getClass(exception);
        assert (state.getClassInitInfo().getInitializationState(exception.getClassName(), state.getJBCOptions()) == InitStatus.YES) : exception
            + " not initialized!";
        OpCode.throwException(state, exceptionClass);
    }

    /**
     * Create an exception instance based on the provided classname and throw
     * it.
     * @param state the state to work with
     * @param exceptionClass the class of the exception to be created and thrown
     */
    private static void throwException(final State state, final IClass exceptionClass) {
        // Create a new instance for the exception
        New.fillState(state, exceptionClass);
        // Get the reference
        final StackFrame currentFrame = state.getCurrentStackFrame();
        // ...but first run the constructor
        final IMethod constructor = exceptionClass.getLocalMethod("<init>", new ParsedMethodDescriptor("()V"));
        InvokeMethod.addNewStackFrame(state, constructor, false, false);
        final AbstractVariableReference exceptionRef = currentFrame.popOperandStack();
        // Mark the stack frame so that the new exception will be handled...
        currentFrame.setException(exceptionRef);

        // clear operand stack
        currentFrame.getOperandStack().getStack().clear();
    }

    /**
     * @return a unique id of this opcode
     */
    public final int getId() {
        return this.id;
    }

    /**
     * @return set of opcodes that might be reached through executing this opcode. This does NOT include exception
     * handlers!
     */
    public Set<OpCode> getAllPossibleSuccessors() {
        if (this.nextOp != null) {
            return Collections.singleton(this.nextOp);
        }
        return Collections.emptySet();
    }

    /**
     * @return true iff there is at least one exception handler
     */
    public boolean hasExceptionHandler() {
        return !this.exceptionTable.isEmpty();
    }

    /**
     * @param preEval some state.
     * @param postEval state obtained from <code>preEval</code> by plain
     * evaluation.
     * @param postEvalInst instance of <code>postEval</code>.
     * @param refMap mapping from references in <code>postEval</code> to their
     *  counterparts in <code>postEvalInst</code>.
     *
     * @return <code>preEvalInst</code>, an instance of <code>preEval</code>
     *  such that <code>postEvalInst</code> is obtained from it by plain
     *  evaluation.
     */
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        throw new NotYetImplementedException();
    }

    /**
     * Sets values of local variables to sensible values. As the set of active
     * local variables may change in evaluation, variables can become inactive
     * and then contain garbage. In backwards evaluation, we need to replace
     * this garbage by more useful things explicitly.
     *
     * @param preEvalAbstr some state
     * @param postEvalAbstr some state obtained from <code>preEvalAbstr</code>
     *  by plain evaluation.
     * @param curWitness a concrete state corresponding to preEvalAbstr
     * @param refMap mapping from references in <code>postEval</code> to their
     *  counterparts in <code>curWitness</code>.
     */
    public void handleActiveVarChangesInRevEv(
        final State preEvalAbstr,
        final State postEvalAbstr,
        final State curWitness,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final OpCode nextOpCode = postEvalAbstr.getCurrentOpCode();
        final IMethod ourMethod = this.getMethod();
        final StackFrame curInstFrame = curWitness.getCurrentStackFrame();
        final StackFrame curAbstrFrame = preEvalAbstr.getCurrentStackFrame();

        //Only do something if we stay in the same method:
        if (nextOpCode.getMethod() != ourMethod) {
            return;
        }

        /*
         * For all vars that are active in this opcode, but not in the following,
         * fill in reasonable values:
         */
        final Collection<Integer> nextOpCodeActiveVars = ourMethod.getActiveVariables(nextOpCode.getPos());
        for (final Integer index : ourMethod.getActiveVariables(this.getPos())) {
            if (!nextOpCodeActiveVars.contains(index)) {
                curInstFrame.setLocalVariable(
                    index,
                    State.mapOrCopyRef(preEvalAbstr, curWitness, curAbstrFrame.getLocalVariable(index), refMap));
            }
        }
    }

    /**
     * The default implementation just does the refine, but for field accesses
     * we implement a shortcut.
     * @param state a state
     * @return true iff we need to refine
     */
    public boolean needsRefine(final State state) {
        return this.refine(state, new LinkedHashSet<Pair<State, ? extends EdgeInformation>>());
    }

    /**
     * @param opCode some opcode
     * @return a negative number only if there is no evaluation from this opcode to the one in the argument. A
     * non-negative number indicates the minimal number of opcodes needed for the path.
     */
    public int mayReach(final OpCode opCode) {

        if (this.reachabilityCache.containsKey(opCode)) {
            synchronized (this.reachabilityCache) {
                return this.reachabilityCache.get(opCode);
            }
        }

        int shortest = Integer.MAX_VALUE;

        final Collection<OpCode> seen = new LinkedHashSet<>();

        final LinkedList<Pair<OpCode, Integer>> todo = new LinkedList<>();
        todo.add(new Pair<>(this, 0));
        while (!todo.isEmpty()) {
            final Pair<OpCode, Integer> current = todo.pop();
            final OpCode currentOpCode = current.x;
            if (current.y >= shortest) {
                continue;
            }
            if (!seen.add(currentOpCode)) {
                continue;
            }
            if (currentOpCode.equals(opCode)) {
                if (current.y < shortest) {
                    shortest = current.y;
                }
            }
            for (final OpCode pred : currentOpCode.getAllPossibleSuccessors()) {
                todo.add(new Pair<>(pred, current.y + 1));
            }
            for (final Pair<ClassName, OpCode> handler : currentOpCode.getExceptionTable()) {
                todo.add(new Pair<>(handler.y, current.y + 1));
            }
        }
        final int res = shortest == Integer.MAX_VALUE ? -1 : shortest;

        if (!this.reachabilityCache.containsKey(opCode)) {
            synchronized (this.reachabilityCache) {
                this.reachabilityCache.put(opCode, res);
            }
        }

        return res;
    }

    public abstract int getNumberOfArguments();
    public abstract int getNumberOfOutputs();

    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Method", this.method.toJSON());
        res.put("OpcodeIndex", this.getPos());
        return res;
    }

}
