package aprove.verification.oldframework.Bytecode.Parser;

import java.io.*;
import java.util.*;

import org.json.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.OpCodes.Branch.*;
import aprove.verification.oldframework.Bytecode.OpCodes.InvokeMethod.*;
import aprove.verification.oldframework.Bytecode.Parser.Attributes.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Completely parsed representation of Java Bytecode methods.
 * @author Marc Brockschmidt
 * @author Fabian K&uuml;rten
 */
public class ParsedMethod implements IMethod {
    /**
     * Table of parsed opcodes. Contains NULL pointers wherever the original
     * bytecode array had arguments.
     */
    private final OpCode[] opcodeTable;

    /**
     * Mutex for {@link #getLocalMethodCalls()}
     */
    private final Object localMethodCallsMutex = new Object();

    /**
     * Mutex for {@link #getMethodCallsRecursively()}
     */
    private final Object methodCallsRecursivelyMutex = new Object();

    /**
     * The raw, underlying method instance, created when parsing the original
     * class file. Contains some useful information such as the method name and
     * access flags.
     */
    private final RawMethod method;

    /**
     * The descriptor of this method.
     */
    private final ParsedMethodDescriptor descriptor;

    /**
     * Map from local variable indexes to local variable table entries matching
     * that index. Used to get variable names for output.
     */
    private CollectionMap<Integer, LocalVariableTableEntry> localVariableInformation;

    /**
     * The enclosing parsed class.
     */
    private final IClass parsedClass;

    /**
     * The results of our used variable analysis.
     */
    private final MethodUsedVariables usedVariables;

    /**
     * The methods called by <em>this</em> method.
     */
    private volatile Set<Pair<Integer, MethodIdentifier>> localCalledMethods;

    /**
     * The transitive closure of methods called by this method.
     */
    private volatile Collection<MethodIdentifier> recursivelyCalledMethods;

    /**
     * Marks how many invocations of methods are happening.
     */
    private Integer numberOfMethodCalls;

    /**
     * Marks how many loop-like structures there are in this method.
     * Maps the start of a loop-like structure (the target of a GOTO) to the
     * last end of it (i.e. the GOTO with the maximal index)
     */
    private Integer numberOfLoops;

    /**
     * Number of calls to other methods that occur in a loop.
     */
    private Integer numberOfCallsInLoops;

    /**
     * Maps the start of a loop-like structure (the target of a GOTO) to the
     * last end of it (i.e. the GOTO with the maximal index)
     */
    private Map<Integer, Integer> loopStartToLoopEndMap;

    /**
     * Maps method identifiers to the number of different call sites to that
     * method in this method.
     */
    private Map<MethodIdentifier, Integer> methodIdToCallNumberMap;

    /**
     * Marks how many loop-like structures there are in this method.
     */
    private Integer numberOfBranches;

    /**
     * Marks if the method writes to an object.
     */
    private Boolean writesToObjects;

    /**
     * Marks if the method reads from an object.
     */
    private Boolean readsFromObjects;

    /**
     * Marks if the method checks some integer value in a branch instructions
     * that jumps behind a goto (i.e. probably a loop).
     */
    private Boolean hasIntInLoopCondition;

    /**
     * Marks if the approximated call graph indicates that this method may
     * eventually lead to a call to itself.
     */
    private Boolean isRecursive;

    Set<ClassName> classesWithExplicitAccess = new LinkedHashSet<>();

    /**
     * Creates a new instance of a parsed method.
     * @param m The raw, underlying method instance.
     * @param opcodeT Table of parsed opcodes.
     * @param parsedC The enclosing parsed class.
     */
    public ParsedMethod(final RawMethod m, final OpCode[] opcodeT, final IClass parsedC) {
        this.method = m;
        this.parsedClass = parsedC;
        this.descriptor = new ParsedMethodDescriptor(this.method.getDescriptor());
        this.opcodeTable = opcodeT;

        if (this.opcodeTable == null) {
            this.localVariableInformation = null;
            this.usedVariables = null;
            return;
        }
        this.usedVariables = new MethodUsedVariables(this);
        this.analyzeExceptionTable();
        this.analyzeLocalVariableTable();
    }

    /**
     * Analyzes the exception table to find out which entries are relevant for
     * each opcodes and stores its results for later use in each opcode.
     */
    private void analyzeExceptionTable() {
        final ExceptionTableEntry[] exceptionTable = this.method.getCodeAttr().getExceptionHandlerTable();

        if (exceptionTable.length > 0) {
            OpCode curOpCode = this.opcodeTable[0];
            while (curOpCode != null) {
                for (final ExceptionTableEntry t : exceptionTable) {
                    if (t.posIsHandled(curOpCode.getPos())) {
                        curOpCode.addExceptionHandler(
                            t.getHandledExceptionClass(),
                            this.opcodeTable[t.getHandlerPosition()]);
                    }
                }
                curOpCode = curOpCode.getNextOp();
            }
        }
    }

    /**
     * Analyzes the local variable table to find out which entries are relevant
     * for which local variable index and stores its results for later use in
     * <code>localVariableInformation</code>.
     */
    private void analyzeLocalVariableTable() {
        if (this.method.getCodeAttr().getLocalVariableTableAttribute() == null) {
            this.localVariableInformation = null;
            return;
        }
        this.localVariableInformation = new CollectionMap<>();

        for (final LocalVariableTableEntry lvtE : this.method.getCodeAttr().getLocalVariableTableAttribute().getTable())
        {
            this.localVariableInformation.add(lvtE.getLocalVarIndex(), lvtE);
        }
    }

    /**
     * Detects all possible method calls in this method, except constructors for
     * exceptions thrown by the JVM and class initializers. This includes calls
     * to methods which might be overriden by a subclass. I.e., if
     * <code>java.lang.Object.toString()</code> is called, we add <em>every</em>
     * <code>toString()</code> method. The result only contains direct calls,
     * see getMethodCallsRecursively().
     * @return possibly called methods
     */
    private Set<Pair<Integer, MethodIdentifier>> analyzeMethodCalls() {
        if (this.isNative() || this.isAbstract()) {
            return Collections.emptySet();
        }

        // The class path, needed to get type information
        final ClassPath cPath = this.parsedClass.getClassPath();

        // find the methods that may be invoked. The identifier gives the
        final Set<Pair<Integer, MethodIdentifier>> methodCalls = new LinkedHashSet<>();

        // Collect the method declarations, we need to find all implementations.
        final LinkedList<Triple<MethodIdentifier, ClassName, Integer>> todo = new LinkedList<>();

        for (final OpCode opCode : this.opcodeTable) {
            // Get all methods possibly called from this opcode.
            if (!(opCode instanceof InvokeMethod)) {
                continue;
            }
            final InvokeMethod invokeMethod = (InvokeMethod) opCode;

            final IMethod resolvedMethod = invokeMethod.resolveMethod();
            if (resolvedMethod == null) {
                // the VM would throw some exception, not interesting here
                continue;
            }

            switch (invokeMethod.getInvocationType()) {
            case SPECIAL:
                /*
                 * For INVOKESPECIAL we can find the invoked method at compile
                 * time (i.e., here and now).
                 */
                final IMethod targetMethod = invokeMethod.getTargetMethod(null, this.parsedClass.getClassPath());
                if (targetMethod == null) {
                    break;
                }
                methodCalls.add(new Pair<>(opCode.getPos(), targetMethod.getMethodIdentifier()));
                break;
            case STATIC:
                /*
                 * For INVOKESTATIC the invoked method is just the resolved
                 * method.
                 */
                methodCalls.add(new Pair<>(opCode.getPos(), resolvedMethod.getMethodIdentifier()));
                break;
            case INTERFACE:
            case VIRTUAL:
                /*
                 * For INVOKEINTERFACE and INVOKEVIRTUAL we need to find the implementations starting in the class of
                 * the resolved method. For INVOKEINTERFACE the specification ensures that the invoked method is in a
                 * class that implements the interface of the resolved method.
                 */
                todo.add(new Triple<>(resolvedMethod.getMethodIdentifier(), resolvedMethod.getClassName(), opCode
                    .getPos()));
                break;
            case DYNAMIC:
                break;
            default:
                assert (false);
                break;
            }
        }

        while (!todo.isEmpty()) {
            final Triple<MethodIdentifier, ClassName, Integer> triple = todo.pop();
            /*
             * Now we have the MethodIdentifier of the called method,
             * however there might be many different methods called, since it
             * might be overriden by a subclass.
             */
            final ClassName className = triple.y;
            final TypeTree typeTree = cPath.getTypeTree(className);
            final MethodIdentifier methodIdentifier = triple.x;
            final int pos = triple.getZ();

            // Get possible overrides
            final IClass targetClass = cPath.getClass(className);
            final IMethod declaredMethod = targetClass.getLocalMethod(methodIdentifier);
            if (declaredMethod != null) {
                methodCalls.add(new Pair<>(pos, new MethodIdentifier(
                    className,
                    methodIdentifier.getMethodName(),
                    methodIdentifier.getDescriptor())));
            }

            // Now consider every subclass of the type the method is invoked on
            if (typeTree.isInterface()) {
                for (final TypeTree subType : typeTree.getImplementingTypes()) {
                    final ClassName subClassName = subType.getClassName();
                    todo.push(new Triple<>(methodIdentifier, subClassName, pos));
                }
            } else {
                for (final TypeTree subType : typeTree.getSubTypes()) {
                    final ClassName subClassName = subType.getClassName();
                    todo.push(new Triple<>(methodIdentifier, subClassName, pos));
                }
            }
        }
        return methodCalls;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getLocalMethodCalls()
     */
    @Override
    public Set<Pair<Integer, MethodIdentifier>> getLocalMethodCalls() {
        if (this.localCalledMethods == null) {
            synchronized (this.localMethodCallsMutex) {
                if (this.localCalledMethods == null) {
                    this.localCalledMethods = this.analyzeMethodCalls();
                }
            }
        }
        return this.localCalledMethods;
    }

    /**
     * Computes the methods recursively called by this method.
     * @return the method recursively called by this method
     */
    private Set<MethodIdentifier> analyzeMethodCallsRecursively() {
        final ClassPath cPath = this.parsedClass.getClassPath();

        final Set<MethodIdentifier> checkedMethods = new LinkedHashSet<>();
        final Set<MethodIdentifier> allCalledMethods = new LinkedHashSet<>();

        final Queue<MethodIdentifier> toCheck = new LinkedList<>();
        toCheck.add(this.getMethodIdentifier());
        while (!toCheck.isEmpty()) {
            final MethodIdentifier current = toCheck.poll();
            if (checkedMethods.contains(current)) {
                continue;
            }
            checkedMethods.add(current);

            final IClass pC = cPath.getClass(current.getClassName());

            final IMethod parsedMethod = pC.getLocalMethod(current);
            final Collection<Pair<Integer, MethodIdentifier>> calledMethods = parsedMethod.getLocalMethodCalls();
            for (final Pair<Integer, MethodIdentifier> pair : calledMethods) {
                allCalledMethods.add(pair.y);
                toCheck.add(pair.y);
            }
        }
        return allCalledMethods;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getMethodCallsRecursively()
     */
    @Override
    public Collection<MethodIdentifier> getMethodCallsRecursively() {
        if (this.recursivelyCalledMethods == null) {
            synchronized (this.methodCallsRecursivelyMutex) {
                if (this.recursivelyCalledMethods == null) {
                    this.recursivelyCalledMethods = this.analyzeMethodCallsRecursively();
                }
            }
        }
        return this.recursivelyCalledMethods;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isRecursive()
     */
    @Override
    public boolean isRecursive() {
        if (this.isRecursive == null) {
            if (this.getMethodCallsRecursively().contains(this.getMethodIdentifier())) {
                this.isRecursive = true;
            } else {
                this.isRecursive = false;
            }
        }
        return this.isRecursive;
    }

    /**
     * Analyze the byte code of this method and gather information about loops,
     * which then can be used in some strange heuristics.
     */
    private void analyzeBytecode() {
        int invokeCount = 0;
        int loopCount = 0;
        final Map<Integer, Integer> loopStartToEnd = new LinkedHashMap<>();
        final Map<MethodIdentifier, Integer> numberOfCalls = new DefaultValueMap<>(0);
        int branchCount = 0;
        int numOfCallsInLoops = 0;
        boolean writes = false;
        boolean reads = false;
        boolean hasIntLoop = false;
        for (final OpCode opCode : this.opcodeTable) {
            if (opCode instanceof Branch) {
                /*
                 * Check the target of the jump. If the instruction before that
                 * is a goto jumping back, this is jumping _over_ the loop, otherwise
                 * it's probably an if.
                 */
                final Branch b = (Branch) opCode;
                if (b.getCompT() != Branch.ComparisonType.JMP) {
                    final OpCode pre = b.getBranchTarget().getLastOp();
                    if (pre instanceof Branch && ((Branch) pre).isGoto() && ((Branch) pre).getBranchOffset() < 0) {
                        if (b.getCompT() != ComparisonType.NULL && b.getCompT() != ComparisonType.NONNULL) {
                            hasIntLoop = true;
                        }
                        final int loopStartPos = b.getBranchTarget().getPos();
                        if (loopStartToEnd.containsKey(loopStartPos)) {
                            loopStartToEnd.put(b.getPos(), Math.max(loopStartPos, loopStartToEnd.get(b.getPos())));
                        } else {
                            loopStartToEnd.put(b.getPos(), loopStartPos);
                        }
                        loopCount++;
                    } else {
                        branchCount++;
                    }
                }
            } else if (opCode instanceof FieldAccess) {
                final FieldAccess fA = (FieldAccess) opCode;
                if (fA.getReadWriteType() == FieldAccess.FieldAccessRW.WRITE) {
                    writes = true;
                } else {
                    reads = true;
                }
            }
        }

        for (final OpCode opCode : this.opcodeTable) {
            //Also catch calls to constructors of new data structures:
            if (opCode instanceof InvokeMethod) {
                final InvokeMethod inv = (InvokeMethod) opCode;
                if (!writes) {
                    if (inv.getInvocationType() == InvocationType.SPECIAL) {
                        final IMethod calledConstructor = inv.resolveMethod();
                        if (calledConstructor != null && !calledConstructor.isNative()) {
                            OpCode firstInst = calledConstructor.getStart();
                            while (firstInst != null) {
                                if (firstInst instanceof FieldAccess
                                    && ((FieldAccess) firstInst).getReadWriteType().equals(
                                        FieldAccess.FieldAccessRW.WRITE))
                                {
                                    writes = true;
                                    break;
                                }
                                firstInst = firstInst.getNextOp();
                            }
                        }
                    }
                }

                //Don't count constructors:
                if (inv.getInvocationType() != InvocationType.SPECIAL) {
                    invokeCount++;
                    final MethodIdentifier methodId = inv.getMethodIdentifier();
                    numberOfCalls.put(methodId, numberOfCalls.get(methodId) + 1);
                }

                final int pos = opCode.getPos();
                for (final Map.Entry<Integer, Integer> e : loopStartToEnd.entrySet()) {
                    final int start = e.getKey();
                    final int end = e.getValue();
                    if (pos >= start && pos <= end) {
                        numOfCallsInLoops++;
                        break;
                    }
                }
            }
        }
        this.methodIdToCallNumberMap = numberOfCalls;
        this.numberOfMethodCalls = invokeCount;
        this.numberOfLoops = loopCount;
        this.numberOfBranches = branchCount;
        this.numberOfCallsInLoops = numOfCallsInLoops;
        this.loopStartToLoopEndMap = loopStartToEnd;
        this.writesToObjects = writes;
        this.readsFromObjects = reads;
        this.hasIntInLoopCondition = hasIntLoop;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getNumberOfMethodCalls(aprove.verification.oldframework.Bytecode.Parser.MethodIdentifier)
     */
    @Override
    public int getNumberOfMethodCalls(final MethodIdentifier methodId) {
        if (this.methodIdToCallNumberMap == null) {
            this.analyzeBytecode();
        }
        return this.methodIdToCallNumberMap.get(methodId);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getNumberOfMethodCalls()
     */
    @Override
    public int getNumberOfMethodCalls() {
        if (this.numberOfMethodCalls == null) {
            this.analyzeBytecode();
        }
        return this.numberOfMethodCalls;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getNumberOfLoops()
     */
    @Override
    public int getNumberOfLoops() {
        if (this.numberOfLoops == null) {
            this.analyzeBytecode();
        }
        return this.numberOfLoops;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getNumberOfCallsInLoops()
     */
    @Override
    public int getNumberOfCallsInLoops() {
        if (this.numberOfCallsInLoops == null) {
            this.analyzeBytecode();
        }
        return this.numberOfCallsInLoops;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getNumberOfBranches()
     */
    @Override
    public int getNumberOfBranches() {
        if (this.numberOfBranches == null) {
            this.analyzeBytecode();
        }
        return this.numberOfBranches;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#writesObjects()
     */
    @Override
    public boolean writesObjects() {
        if (this.writesToObjects == null) {
            this.analyzeBytecode();
        }
        return this.writesToObjects;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#readsObjects()
     */
    @Override
    public boolean readsObjects() {
        if (this.readsFromObjects == null) {
            this.analyzeBytecode();
        }
        return this.readsFromObjects;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#hasIntLoop()
     */
    @Override
    public boolean hasIntLoop() {
        if (this.hasIntInLoopCondition == null) {
            this.analyzeBytecode();
        }
        return this.hasIntInLoopCondition;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#usesRandom()
     */
    @Override
    public boolean usesRandom() {
        for (final Pair<Integer, MethodIdentifier> e : this.localCalledMethods) {
            if (e.getValue().getClassName().getClassName().startsWith("Random")) {
                return true;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isInLoop(int)
     */
    @Override
    public boolean isInLoop(final int pos) {
        if (this.loopStartToLoopEndMap == null) {
            this.analyzeBytecode();
        }
        for (final Map.Entry<Integer, Integer> e : this.loopStartToLoopEndMap.entrySet()) {
            final int start = e.getKey();
            final int end = e.getValue();
            if (pos >= start && pos <= end) {
                return true;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getDescriptor()
     */
    @Override
    public ParsedMethodDescriptor getDescriptor() {
        return this.descriptor;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getName()
     */
    @Override
    public String getName() {
        return this.method.getName();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getVarArrayLength()
     */
    @Override
    public int getVarArrayLength() {
        return this.method.getCodeAttr().getMaxLocalVarNumber();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getOpStackHeight()
     */
    @Override
    public int getOpStackHeight() {
        return this.method.getCodeAttr().getMaxStackHeight();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getClassName()
     */
    @Override
    public ClassName getClassName() {
        return this.parsedClass.getClassName();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getMethodIdentifier()
     */
    @Override
    public MethodIdentifier getMethodIdentifier() {
        return new MethodIdentifier(this.getClassName(), this.getName(), this.getDescriptor());
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getParsedClass()
     */
    @Override
    public IClass getIClass() {
        return this.parsedClass;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getOpcodeAt(int)
     */
    @Override
    public OpCode getOpcodeAt(final int index) {
        assert (this.opcodeTable[index] != null);
        return this.opcodeTable[index];
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getStart()
     */
    @Override
    public OpCode getStart() {
        return this.getOpcodeAt(0);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#getLocalVariableName(int, int)
     */
    @Override
    public String getLocalVariableName(final int localVarIndex, final int position) {
        if (this.localVariableInformation == null) {
            return null;
        }

        final Collection<LocalVariableTableEntry> entriesForIndex =
            this.localVariableInformation.getNotNull(localVarIndex);
        for (final LocalVariableTableEntry lvtE : entriesForIndex) {
            if (lvtE.positionInScope(position)) {
                return lvtE.getVarName();
            }
        }
        return null;
    }

    /**
     * @param position Some bytecode position.
     * @return A list of local variable registers which are in use at <code>
     *  position</code>
     * .
     */
    @Override
    public List<Integer> getActiveVariables(final int position) {
        return new ArrayList<Integer>(usedVariables.usedAt(position));
    }

    /**
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isStatic()
     * @return true iff this method is marked as static
     */
    @Override
    public boolean isStatic() {
        return this.method.isStatic();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isStrictFP()
     */
    @Override
    public boolean isStrictFP() {
        return this.method.isStrictFP();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isSynchronized()
     */
    @Override
    public boolean isSynchronized() {
        return this.method.isSynchronized();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isNative()
     */
    @Override
    public boolean isNative() {
        return this.method.isNative();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isAbstract()
     */
    @Override
    public boolean isAbstract() {
        return this.method.isAbstract();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isFinal()
     */
    @Override
    public boolean isFinal() {
        return this.method.isFinal();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isProtected()
     */
    @Override
    public boolean isProtected() {
        return this.method.isProtected();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isPrivate()
     */
    @Override
    public boolean isPrivate() {
        return this.method.isPrivate();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isPublic()
     */
    @Override
    public boolean isPublic() {
        return this.method.isPublic();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isDefaultAccess()
     */
    @Override
    public boolean isDefaultAccess() {
        return this.method.isDefaultAccess();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isInstanceInitializer()
     */
    @Override
    public boolean isInstanceInitializer() {
        return "<init>".equals(this.method.getName()) && this.descriptor.getReturnType() == null;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isClassInitializer()
     */
    @Override
    public boolean isClassInitializer() {
        if (this.parsedClass.getClassFileVersion().x >= 51) {
            if (!this.isStatic()) {
                return false;
            }
        }
        return "<clinit>".equals(this.method.getName())
            && this.getDescriptor().getArgumentCount() == 0
            && this.descriptor.getReturnType() == null;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#toString()
     */
    @Override
    public String toString() {
        return (this.isPublic() ? "public " : "")
            + (this.isProtected() ? "protected " : "")
            + (this.isPrivate() ? "private " : "")
            + (this.isAbstract() ? "abstract " : "")
            + (this.isStatic() ? "static " : "")
            + (this.isFinal() ? "final " : "")
            + (this.isSynchronized() ? "synchronized " : "")
            + (this.isNative() ? "native " : "")
            + (this.isStrictFP() ? "strictfp " : "")
            + this.getName()
            + this.getDescriptor();

    }

    /**
     * Parse a fully qualified method name with sig, such as
     * "class.name.method(I[I)V".
     * @param fqName A fully qualified method name, including type descriptor.
     * @return Triple of class name, method name and method descriptor.
     */
    public static MethodIdentifier parseFullyQualifiedMethodNameWithSig(final String fqName) {
        if (Globals.useAssertions) {
            assert fqName != null : "methodname is NULL";
            assert fqName.contains("(") : "methodname is not fully qualified";
        }
        final String classPortion = fqName.substring(0, fqName.indexOf('('));
        final ClassName className = ClassName.fromDotted(classPortion.substring(0, classPortion.lastIndexOf('.')));
        final String methodNameAndSig = fqName.substring(classPortion.lastIndexOf('.') + 1);
        final String methodName = methodNameAndSig.substring(0, methodNameAndSig.indexOf('('));
        final ParsedMethodDescriptor methodSig =
            new ParsedMethodDescriptor(methodNameAndSig.substring(methodNameAndSig.indexOf('(')));
        return new MethodIdentifier(className, methodName, methodSig);
    }

    /**
     * Throw to indicate that the requested method name has more than one match.
     */
    public static class AmbigousMethodIdentifierException extends RuntimeException {
        /**
         * @param text the input
         * @param a first match
         * @param b second match
         */
        public AmbigousMethodIdentifierException(final String text, final MethodIdentifier a, final MethodIdentifier b)
        {
            super("More than one match for '" + text + "'. Found at least: '" + a + "' and '" + b + "'.");
        }
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isMain()
     */
    @Override
    public boolean isMain() {
        if (!this.isPublic()) {
            return false;
        }
        if (!this.isStatic()) {
            return false;
        }
        if (this.descriptor.getReturnType() != null) {
            return false;
        }
        if (!"main".equals(this.getMethodIdentifier().getMethodName())) {
            return false;
        }
        if (this.descriptor.getArgumentCount() != 1) {
            return false;
        }
        final FuzzyType inputArgsType =
            new FuzzyClassType(ClassName.Important.JAVA_LANG_STRING.getClassName(), true, 1);
        return this.descriptor.getType(0).equals(inputArgsType);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isSignaturePolymorphic()
     */
    @Override
    public boolean isSignaturePolymorphic() {
        if (!this.isNative()) {
            return false;
        }
        if (!this.isVarArgs()) {
            return false;
        }
        if (this.getDescriptor().getArgumentCount() != 1) {
            return false;
        }
        if (!"java/lang/invoke".equals(this.getIClass().getClassName().getPkgName())) {
            return false;
        }
        if (!"MethodHandle".equals(this.getIClass().getClassName().getClassName())) {
            return false;
        }
        if (!FuzzyClassType.FT_JAVA_LANG_OBJECT.equals(this.getDescriptor().getReturnType())) {
            return false;
        }
        final FuzzyType ft = this.getDescriptor().getType(0);
        if (ft.isArrayType() && ft.getArrayDimension() == 1) {
            final FuzzyType enclosedType = ft.getEnclosedType();
            if (FuzzyClassType.FT_JAVA_LANG_OBJECT.equals(enclosedType)) {
                return true;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#isVarArgs()
     */
    @Override
    public boolean isVarArgs() {
        return this.method.isVarArgs();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#toJSON()
     */
    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Name", this.parsedClass.getClassName().toString() + "." + this.getName());
        res.put("Descriptor", this.descriptor.toString());
        return res;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedMethod#dumpMethodInfo(java.lang.String)
     */
    @Override
    public void dumpMethodInfo(String fileName) {
        analyzeBytecode();
        try (PrintWriter writer = new PrintWriter(new BufferedWriter(new FileWriter(fileName)))) {
            writer.println(parsedClass.getClassName() + "." + method.getName() + descriptor);
            writer.println("number of loops: " + numberOfLoops);
            writer.println("number of branches: " + numberOfBranches);
            writer.println("called methods: " + methodIdToCallNumberMap);
            writer.println("number of method calls in loops: " + numberOfCallsInLoops);
            writer.println("writes to objects: " + writesToObjects);
            writer.println("reads from objects: " + readsFromObjects);
            writer.println("some loop condition depends on integers: " + hasIntInLoopCondition);
            writer.println("strict fp: " + isStrictFP());
            writer.println("synchronized: " + isSynchronized());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public boolean variableUsedAt(int varIndex, int pos) {
        return usedVariables.usedAt(pos).contains(varIndex);
    }

    @Override
    public boolean wasMarkedAsAccessibleBy(ClassName className) {
        return classesWithExplicitAccess.contains(className);
    }

    @Override
    public void setAccessible(ClassName className) {
        classesWithExplicitAccess.add(className);
    }

}
