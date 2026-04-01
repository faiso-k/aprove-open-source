package aprove.verification.oldframework.Bytecode.Parser;

import static aprove.verification.oldframework.Bytecode.Parser.OpcodeConstants.*;

import java.util.*;

import aprove.*;
import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.OpCodes.Branch.*;
import aprove.verification.oldframework.Bytecode.OpCodes.CheckCast.*;
import aprove.verification.oldframework.Bytecode.OpCodes.ConstantStackPush.*;
import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.OpCodes.FloatArithmetic.*;
import aprove.verification.oldframework.Bytecode.OpCodes.InvokeMethod.*;
import aprove.verification.oldframework.Bytecode.Parser.Attributes.*;
import aprove.verification.oldframework.Bytecode.Parser.ConstantPool.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Fully parsed representation of a bytecode class.
 * @author Marc Brockschmidt, Christian von Essen
 */
public class ParsedClass implements IClass {
    /**
     * The parsed class file, containing some more low-level information.
     */
    private final ParsedClassFile classFile;

    /**
     * Fully qualified identifier of the parsed class
     */
    private ClassName className;

    /**
     * Methods provided in this class, indexed by their name and descriptor.
     */
    private final Map<String, Map<ParsedMethodDescriptor, ParsedMethod>> methodMap;

    /**
     * The class path in which this class is to be used.
     */
    private final ClassPath classPath;

    /**
     * Map of field names to the field objects for all static fields.
     */
    private final ImmutableMap<String, Field> staticFields;

    /**
     * Map of field names to the field objects for all instance fields.
     */
    private final ImmutableMap<String, Field> instanceFields;

    /**
     * The type tree of this class.
     */
    private final TypeTree typeTree;

    private ClassStreamProvider.Type classStreamProviderType;

    /**
     * Parse a class file made available through the provided input stream.
     * @param classF the parsed raw class file
     * @param cPath The considered class path for this analysis.
     * @param typeTreeParam the type tree of this class
     */
    public ParsedClass(final ParsedClassFile classF, final ClassPath cPath, final TypeTree typeTreeParam, ClassStreamProvider.Type classStreamProviderType) {
        this.classFile = classF;
        this.className = this.classFile.getClassName();
        this.classPath = cPath;
        this.typeTree = typeTreeParam;
        this.classStreamProviderType = classStreamProviderType;

        // make sure we also have ParsedClass objects for all super types
        final TypeTree superType = typeTreeParam.getSuperType();
        if (superType != null) {
            this.classPath.getClass(superType.getClassName());
        }
        for (final TypeTree implementedInterface : typeTreeParam.getImplementedInterfaces()) {
            this.classPath.getClass(implementedInterface.getClassName());
        }

        this.methodMap = new LinkedHashMap<String, Map<ParsedMethodDescriptor, ParsedMethod>>();

        final Map<String, Field> instanceFieldsMutable = new LinkedHashMap<String, Field>();
        final Map<String, Field> staticFieldsMutable = new LinkedHashMap<String, Field>();

        for (final RawMethod method : this.classFile.getMethods()) {
            final ParsedMethod m;
            OpCode[] opcodeTable = null;
            if (method.getCodeAttr() == null) {
                m = new ParsedMethod(method, null, this);
            } else {
                opcodeTable = this.parseByteCode(method.getCodeAttr().getBytecode());
                m = new ParsedMethod(method, opcodeTable, this);
            }
            // Every opcode has a reference to the method containing it
            // Set those links here
            if (opcodeTable != null) {
                OpCode t = opcodeTable[0];
                while (t != null) {
                    t.setMethod(m);
                    t = t.getNextOp();
                }
            }
            final String methodName = m.getName();
            Map<ParsedMethodDescriptor, ParsedMethod> innerMap = this.methodMap.get(methodName);
            if (innerMap == null) {
                innerMap = new LinkedHashMap<ParsedMethodDescriptor, ParsedMethod>();
                this.methodMap.put(methodName, innerMap);
            }
            assert (innerMap.get(m.getDescriptor()) == null);
            innerMap.put(m.getDescriptor(), m);
        }

        // parse fields
        for (final Field field : this.classFile.getClassFields()) {
            staticFieldsMutable.put(field.getName(), field);
        }
        for (final Field field : this.classFile.getInstanceFields()) {
            instanceFieldsMutable.put(field.getName(), field);
        }
        this.instanceFields = ImmutableCreator.create(instanceFieldsMutable);
        this.staticFields = ImmutableCreator.create(staticFieldsMutable);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getClassStreamProviderType()
     */
    @Override
    public ClassStreamProvider.Type getClassStreamProviderType() {
        return classStreamProviderType;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getClassName()
     */
    @Override
    public ClassName getClassName() {
        return this.className;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder r = new StringBuilder();
        r.append(this.className);
        r.append("\n");
        for (final Map.Entry<String, Map<ParsedMethodDescriptor, ParsedMethod>> e : this.methodMap.entrySet()) {
            r.append("Methods with name " + e.getKey() + ":\n");
            for (final IMethod m : e.getValue().values()) {
                r.append(m.getDescriptor());
                r.append("\n");
            }
            r.append("\n");
        }

        return r.toString();
    }

    /**
     * Parse the actual bytecode array provided for a method
     * @param methodBytecode bytecode array
     * @return array of opcodes, where each index corresponds to the
     *  parsed opcode at that place in <code>methodBytecode</code> or
     *  the NULL pointer if no such opcode existed.
     */
    private OpCode[] parseByteCode(final byte[] methodBytecode) {
        final int bytecodeLength = methodBytecode.length;
        final OpCode[] opcodes = new OpCode[bytecodeLength];
        /* was the "wide" opcode read (this round)? */
        boolean wide = false;
        boolean newWide = false;

        OpCode lastOpCode = null;
        int position = 0;
        while (position < bytecodeLength) {
            final int opc = methodBytecode[position] & 0xFF;
            if (Globals.useAssertions && wide) {
                assert (opc == ILOAD
                    || opc == FLOAD
                    || opc == ALOAD
                    || opc == LLOAD
                    || opc == DLOAD
                    || opc == ISTORE
                    || opc == FSTORE
                    || opc == ASTORE
                    || opc == LSTORE
                    || opc == DSTORE
                    || opc == RET || opc == IINC);
            }
            Pair<OpCode, Integer> t = null;

            if (opc == NOP) {
                t = new Pair<OpCode, Integer>(new Nop(), 0);
            } else if (opc >= ACONST_NULL && opc <= SALOAD) {
                t = this.loadOpCodes(methodBytecode, position, opc, wide);
            } else if (opc >= ISTORE && opc <= SASTORE) {
                t = this.storeOpCodes(methodBytecode, position, opc, wide);
            } else if (opc >= POP && opc <= SWAP) {
                t = this.stackOpCodes(methodBytecode, position, opc, wide);
            } else if (opc >= IADD && opc <= DNEG) {
                t = this.arithmeticOpCodes(methodBytecode, position, opc, wide);
            } else if (opc >= ISHL && opc <= LXOR) {
                t = this.bitOpCodes(methodBytecode, position, opc, wide);

            } else if (opc == IINC) {
                if (wide) {
                    final OpCode currentOpCode =
                        new Inc(
                            (int) getUSignedFromByteArray(methodBytecode, position + 1, 2),
                            (int) getSignedFromByteArray(methodBytecode, position + 3, 2));
                    t = new Pair<OpCode, Integer>(currentOpCode, 4);
                } else {
                    final OpCode currentOpCode =
                        new Inc(
                            (int) getUSignedFromByteArray(methodBytecode, position + 1, 1),
                            (int) getSignedFromByteArray(methodBytecode, position + 2, 1));
                    t = new Pair<OpCode, Integer>(currentOpCode, 2);
                }

            } else if (opc >= I2L && opc <= I2S) {
                t = this.typecastOpCodes(methodBytecode, position, opc, wide);
            } else if (opc >= LCMP && opc <= DCMPG) {
                t = this.compareOpCodes(methodBytecode, position, opc, wide);
            } else if ((opc >= IFEQ && opc <= JSR) || (opc >= IFNULL && opc <= IFNONNULL)) {
                t = this.branchOpCodes(methodBytecode, position, opc, wide);
            } else if (opc == RET) { // Ret, not to be confused with Return!
                final OpCode currentOpCode =
                    new Ret((int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
                t = new Pair<OpCode, Integer>(currentOpCode, wide ? 2 : 1);

            } else if (opc >= TABLESWITCH && opc <= LOOKUPSWITCH) {
                t = this.switchOpCodes(methodBytecode, position, opc, wide);
            } else if (opc >= IRETURN && opc <= RETURN) {
                t = this.returnOpCodes(methodBytecode, position, opc, wide);
            } else if (opc >= GETSTATIC && opc <= PUTFIELD) {
                t = this.fieldAccessOpCodes(methodBytecode, position, opc, wide);
            } else if (opc >= INVOKEVIRTUAL && opc <= INVOKEDYNAMIC) {
                t = this.invocationOpCodes(methodBytecode, position, opc);
            } else if (opc == NEW) {
                final int index = (int) getUSignedFromByteArray(methodBytecode, position + 1, 2);
                // Get all data from the constant pool:

                t = new Pair<OpCode, Integer>(new New(this.classFile.resolveClassNameRef(index)), 2);
            } else if ((opc >= NEWARRAY && opc <= ARRAYLENGTH) || opc == MULTIANEWARRAY) {
                t = this.arrayOpCodes(methodBytecode, position, opc, wide);
            } else if (opc == ATHROW) {
                t = new Pair<OpCode, Integer>(new AThrow(), 0);
            } else if (opc == CHECKCAST || opc == INSTANCEOF) {
                final int index = (int) getUSignedFromByteArray(methodBytecode, position + 1, 2);
                final int typeDescriptionIndex = ((CPClassRef) this.classFile.getConstant(index)).getClassRefIndex();
                final CPString typeDescription = (CPString) this.classFile.getConstant(typeDescriptionIndex);
                final FuzzyType checkedType = FuzzyType.parseType(typeDescription.getString());
                CastCheckType type;
                if (opc == CHECKCAST) {
                    type = CastCheckType.CHECKCAST;
                } else {
                    type = CastCheckType.INSTANCEOF;
                }
                t = new Pair<OpCode, Integer>(new CheckCast(checkedType, type), 2);
            } else if (opc == MONITORENTER || opc == MONITOREXIT) {
                t = new Pair<OpCode, Integer>(new MonitorEnterExit(), 0);
            } else if (opc == WIDE) {
                t = new Pair<OpCode, Integer>(new Nop(), 0);
                wide = true;
                newWide = true;
            } else {
                final String errMsg = "Opcode " + opc + " not supported. Aborting";
                System.err.println(errMsg);
                throw new UnsupportedOperationException(errMsg);
            }

            opcodes[position] = t.x;
            assert (t.x != null);
            // Link last OpCode to this one:
            if (lastOpCode != null) {
                lastOpCode.setNextOp(t.x);
            }
            t.x.setLastOp(lastOpCode);
            t.x.setPos(position);
            lastOpCode = t.x;
            position += 1 + t.y;

            if (newWide) {
                newWide = false;
            } else {
                wide = false;
            }
        }
        assert (!newWide) : "There must be some opcode after each WIDE";

        // OpCodes have been created, do a second pass to fix all references:
        for (position = 0; position < bytecodeLength; position++) {
            if (opcodes[position] instanceof Branch) {
                final Branch t = (Branch) opcodes[position];

                /*
                 * We may point to WIDE or NOP, which are not part of our
                 * bytecode representation. In this case we point to the
                 * following opcode.
                 */
                final OpCode target = getOpCode(opcodes, methodBytecode, position + t.getBranchOffset());
                t.setBranchTarget(target);
            } else if (opcodes[position] instanceof TableSwitch) {
                final int padding = (4 - ((position + 1) % 4)) % 4;
                final int def = (int) getUSignedFromByteArray(methodBytecode, position + padding + 1, 4);
                final TableSwitch ts = (TableSwitch) opcodes[position];
                final int high = ts.getHigh();
                final int low = ts.getLow();
                for (int i = 0; i < (high - low) + 1; i++) {
                    /*
                     * The target may not exist, so we need to find the real
                     * target (see above)
                     */
                    ts
                        .setTarget(
                            i + low,
                            getOpCode(
                                opcodes,
                                methodBytecode,
                                position
                                    + (int) getUSignedFromByteArray(
                                        methodBytecode,
                                        position + padding + 12 + 4 * i + 1,
                                        4)));
                }

                ts.setDefault(opcodes[def + position]);
            } else if (opcodes[position] instanceof LookupSwitch) {
                final LookupSwitch ls = (LookupSwitch) opcodes[position];
                final int padding = (4 - ((position + 1) % 4)) % 4;
                final int def = (int) getUSignedFromByteArray(methodBytecode, position + padding + 1, 4);
                final int npairs = ls.getNpairs();
                for (int i = 0; i < npairs; i++) {
                    final int match =
                        (int) getUSignedFromByteArray(methodBytecode, position + padding + 8 + 4 * (i * 2) + 1, 4);
                    final OpCode target =
                        getOpCode(
                            opcodes,
                            methodBytecode,
                            position
                                + (int) getUSignedFromByteArray(methodBytecode, position
                                    + padding
                                    + 8
                                    + 4
                                    * (i * 2 + 1)
                                    + 1, 4));
                    ls.setTarget(i, match, target);
                }
                assert (opcodes[def + position] != null);
                ls.setDefault(opcodes[def + position]);
            }
        }

        return opcodes;
    }

    /**
     * Because we do not create objects for the opcodes WIDE and NOP, we may
     * point to positions in the code where no opcode object exists. In these
     * cases, just continue with the next valid opcode object.
     * @param opcodes all opcode objects we created
     * @param methodBytecode the byte stream defining the code
     * @param position the position of the opcode we want
     * @return the next valid opcode object for the given position.
     */
    private static OpCode getOpCode(final OpCode[] opcodes, final byte[] methodBytecode, final int position) {
        OpCode target = opcodes[position];
        int currentPosition = position + 1;
        while (target == null) {
            target = opcodes[currentPosition];
            final int opc = methodBytecode[currentPosition - 1] & 0xFF;
            if (opc != NOP && opc != WIDE) {
                throw new RuntimeException();
            }
            currentPosition++;
        }
        return target;
    }

    /**
     * Retrieve an unsigned number from an array of bytes.
     * @param bytes the byte array to fetch data from
     * @param pos the position of the requested data in the byte array
     * @param num the number of bytes to be considered
     * @return the retrieved number
     */
    private static long getUSignedFromByteArray(final byte[] bytes, final int pos, final int num) {
        long r = 0;
        for (int i = 0; i < num; i++) {
            r = (r << 8) | (bytes[pos + i] & 0xFF);
        }

        return r;
    }

    /**
     * Retrieve a signed number from an array of bytes.
     * @param bytes the byte array to fetch data from
     * @param pos the position of the requested data in the byte array
     * @param num the number of bytes to be considered
     * @return the retrieved number
     */
    private static long getSignedFromByteArray(final byte[] bytes, final int pos, final int num) {
        int r = bytes[pos]; // sign-extension
        for (int i = 1; i < num; i++) {
            r = (r << 8) | (bytes[pos + i] & 0xFF);
        }

        return r;
    }

    /**
     * Compute the operand type of a opcode from a number. Through the entire
     * opcode specifications, the same order of operand types for a single
     * operation was used (ie, the first load opcode handles ints, the second
     * longs, ...)
     * @param t number of the operand type
     * @return the operand type, translated into an ENUM
     */
    private static OperandType computeOperandType(final int t) {
        switch (t) {
        case 0:
            return OperandType.INTEGER;
        case 1:
            return OperandType.LONG;
        case 2:
            return OperandType.FLOAT;
        case 3:
            return OperandType.DOUBLE;
        case 4:
            return OperandType.ADDRESS;
        case 5:
            return OperandType.BYTE;
        case 6:
            return OperandType.CHAR;
        case 7:
            return OperandType.SHORT;
        default:
            assert (false) : "Unhandled operand type";
        }
        return null;
    }

    /**
     * Handles load opcodes ([0x01,0x35]) from a (java) bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> loadOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;
        Integer operandBytes = 0;

        //load a constant (indicated by opcode)
        if (opc == ACONST_NULL) {
            currentOpCode = new ConstantStackPush(null, StackPushType.NULL);
        } else if (opc >= ICONST_M1 && opc <= ICONST_5) {
            currentOpCode = new ConstantStackPush(Integer.valueOf(opc - ICONST_0), StackPushType.INTEGER);
        } else if (opc >= LCONST_0 && opc <= LCONST_1) {
            currentOpCode = new ConstantStackPush(Long.valueOf(opc - LCONST_0), StackPushType.LONG);
        } else if (opc >= FCONST_0 && opc <= FCONST_2) {
            currentOpCode = new ConstantStackPush(Float.valueOf(opc - FCONST_0), StackPushType.FLOAT);
        } else if (opc >= DCONST_0 && opc <= DCONST_1) {
            currentOpCode = new ConstantStackPush(Double.valueOf(opc - DCONST_0), StackPushType.DOUBLE);

            //load a constant (indicated by arguments)
        } else if (opc == BIPUSH) {
            currentOpCode =
                new ConstantStackPush(
                    Integer.valueOf((int) getSignedFromByteArray(methodBytecode, position + 1, 1)),
                    StackPushType.INTEGER);
            operandBytes = 1;
        } else if (opc == SIPUSH) {
            currentOpCode =
                new ConstantStackPush(
                    Integer.valueOf((int) getSignedFromByteArray(methodBytecode, position + 1, 2)),
                    StackPushType.INTEGER);
            operandBytes = 2;

            //load a constant (from the constant pool):
        } else if (opc >= LDC && opc <= LDC2_W) {
            //Get an index to the constant pool, note that we have used up
            //argument bytes:
            operandBytes = 1;
            int idx;
            if (opc == LDC) {
                idx = (int) getUSignedFromByteArray(methodBytecode, position + 1, 1);
            } else {
                operandBytes = 2;
                idx = (int) getUSignedFromByteArray(methodBytecode, position + 1, 2);
            }
            //Get the value, not caring about the type yet:
            final CPEntry t = this.classFile.getConstant(idx);

            if (t instanceof CPInteger) {
                currentOpCode = new ConstantStackPush(((CPInteger) t).getInt(), StackPushType.INTEGER);
            } else if (t instanceof CPFloat) {
                currentOpCode = new ConstantStackPush(((CPFloat) t).getFloat(), StackPushType.FLOAT);
            } else if (t instanceof CPLong) {
                currentOpCode = new ConstantStackPush(((CPLong) t).getLong(), StackPushType.LONG);
            } else if (t instanceof CPDouble) {
                currentOpCode = new ConstantStackPush(((CPDouble) t).getDouble(), StackPushType.DOUBLE);
            } else if (t instanceof CPClassRef) {
                final String typeName = this.classFile.resolveStringRef(((CPClassRef) t).getClassRefIndex());
                currentOpCode = new ConstantStackPush(FuzzyType.parseType(typeName), StackPushType.CLASS);
                //Otherwise, t is a reference to a String:
            } else if (t instanceof CPStringRef) {
                final String constantString = this.classFile.resolveStringRef(((CPStringRef) t).getStringRefIndex());
                currentOpCode = new ConstantStackPush(constantString, StackPushType.STRING);
            } else {
                assert (false) : "Unknown constant pool entry marked to be pushed onto stack: " + t;
            }

            // Loading stuff from registers to the stack:
        } else if (opc == ILOAD) {
            currentOpCode =
                new Load(OperandType.INTEGER, (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc == LLOAD) {
            currentOpCode =
                new Load(OperandType.LONG, (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc == FLOAD) {
            currentOpCode =
                new Load(OperandType.FLOAT, (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc == DLOAD) {
            currentOpCode =
                new Load(OperandType.DOUBLE, (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc == ALOAD) {
            currentOpCode =
                new Load(OperandType.ADDRESS, (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc >= ILOAD_0 && opc <= ALOAD_3) {
            /* There are four each opcodes for int, long, float, double and
             * address, and their order is canonical, so we can just check
             * in which block they are, compute the actual type and handle
             * them all at once: */
            final int operandTypeID = ((opc - ILOAD_0) / 4);
            final OperandType opType = computeOperandType(operandTypeID);
            currentOpCode = new Load(opType, opc - (ILOAD_0 + operandTypeID * 4));

            // Loading stuff from an array:
        } else if (opc >= IALOAD && opc <= SALOAD) {
            currentOpCode = new ArrayAccess(computeOperandType(opc - IALOAD), FieldAccessRW.READ);
        }

        return new Pair<OpCode, Integer>(currentOpCode, operandBytes);
    }

    /**
     * Handles store opcodes ([0x36,0x56]) from a (java) bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> storeOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;
        Integer operandBytes = 0;

        // Storing stuff from the stack in registers:
        if (opc == ISTORE) {
            currentOpCode =
                new Store(
                    OperandType.INTEGER,
                    (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc == LSTORE) {
            currentOpCode =
                new Store(OperandType.LONG, (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc == FSTORE) {
            currentOpCode =
                new Store(OperandType.FLOAT, (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc == DSTORE) {
            currentOpCode =
                new Store(OperandType.DOUBLE, (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc == ASTORE) {
            currentOpCode =
                new Store(
                    OperandType.ADDRESS,
                    (int) getUSignedFromByteArray(methodBytecode, position + 1, wide ? 2 : 1));
            operandBytes = wide ? 2 : 1;
        } else if (opc >= ISTORE_0 && opc <= ASTORE_3) {
            /* There are four each opcodes for int, long, float, double and
             * address, and their order is canonical, so we can just check
             * in which block they are, compute the actual type and handle
             * them all at once: */
            final int operandTypeID = ((opc - ISTORE_0) / 4);
            final OperandType opType = computeOperandType(operandTypeID);
            currentOpCode = new Store(opType, opc - (ISTORE_0 + operandTypeID * 4));
        } else if (opc >= IASTORE && opc <= SASTORE) {
            currentOpCode = new ArrayAccess(computeOperandType(opc - IASTORE), FieldAccessRW.WRITE);
        }

        return new Pair<OpCode, Integer>(currentOpCode, operandBytes);
    }

    /**
     * Handles stack opcodes ([0x57,0x5f]) from a (java) bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> stackOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;

        if (opc == POP || opc == POP2) {
            currentOpCode = new StackPop(opc == POP2);
        } else if (opc >= DUP && opc <= DUP2_X2) {
            int wordsToDuplicate = -1;
            int wordsToSkipWhenInserting = -1;
            switch (opc) {
            case DUP:
                wordsToDuplicate = 1;
                wordsToSkipWhenInserting = 1;
                break;
            case DUP_X1:
                wordsToDuplicate = 1;
                wordsToSkipWhenInserting = 2;
                break;
            case DUP_X2:
                wordsToDuplicate = 1;
                wordsToSkipWhenInserting = 3;
                break;
            case DUP2:
                wordsToDuplicate = 2;
                wordsToSkipWhenInserting = 2;
                break;
            case DUP2_X1:
                wordsToDuplicate = 2;
                wordsToSkipWhenInserting = 3;
                break;
            case DUP2_X2:
                wordsToDuplicate = 2;
                wordsToSkipWhenInserting = 4;
                break;
            default:
                assert (false) : "Your JVM is broken";
            }
            currentOpCode = new Duplicate(wordsToDuplicate, wordsToSkipWhenInserting);
        } else if (opc == SWAP) {
            currentOpCode = new Swap();
        }

        return new Pair<OpCode, Integer>(currentOpCode, 0);
    }

    /**
     * Handles opcodes of arithmetic operations ([0x60,0x77]) from a (java)
     * bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> arithmeticOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;
        //final OperandType t = computeOperandType((opc - IADD) % 4);

        if (opc == IADD || opc == LADD) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.ADD, (opc == IADD) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc == FADD || opc == DADD) {
            currentOpCode = new FloatArithmetic(FloatArithType.ADD);
        } else if (opc == ISUB || opc == LSUB) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.SUB, (opc == ISUB) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc == FSUB || opc == DSUB) {
            currentOpCode = new FloatArithmetic(FloatArithType.SUB);
        } else if (opc == IMUL || opc == LMUL) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.MUL, (opc == IMUL) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc == FMUL || opc == DMUL) {
            currentOpCode = new FloatArithmetic(FloatArithType.MUL);
        } else if (opc == IDIV || opc == LDIV) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.TIDIV, (opc == IDIV) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc == FDIV || opc == DDIV) {
            currentOpCode = new FloatArithmetic(FloatArithType.DIV);
        } else if (opc == IREM || opc == LREM) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.TMOD, (opc == IREM) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc == FREM || opc == DREM) {
            currentOpCode = new FloatArithmetic(FloatArithType.REM);
        } else if (opc == INEG || opc == LNEG) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.NEG, (opc == INEG) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc == FNEG || opc == DNEG) {
            currentOpCode = new FloatArithmetic(FloatArithType.NEG);
        }

        return new Pair<OpCode, Integer>(currentOpCode, 0);
    }

    /**
     * Handles opcodes of bit operations ([0x78,0x83]) from a (java) bytecode
     * file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> bitOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;

        if (opc >= ISHL && opc <= LSHL) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.SHL, (opc == ISHL) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc >= ISHR && opc <= LSHR) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.SHR, (opc == ISHR) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc >= IUSHR && opc <= LUSHR) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.USHR, (opc == IUSHR) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc >= IAND && opc <= LAND) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.AND, (opc == IAND) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc >= IOR && opc <= LOR) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.OR, (opc == IOR) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        } else if (opc >= IXOR && opc <= LXOR) {
            currentOpCode =
                new IntArithmetic(ArithmeticOperationType.XOR, (opc == IXOR) ? IntegerType.JAVA_INT : IntegerType.JAVA_LONG);
        }
        return new Pair<OpCode, Integer>(currentOpCode, 0);
    }

    /**
     * Handles opcodes of typecast operations ([0x85,0x93]) from a (java)
     * bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> typecastOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {

        OperandType fromType = null;
        OperandType toType = null;
        switch (opc) {
        case I2L:
            fromType = OperandType.INTEGER;
            toType = OperandType.LONG;
            break;
        case I2F:
            fromType = OperandType.INTEGER;
            toType = OperandType.FLOAT;
            break;
        case I2D:
            fromType = OperandType.INTEGER;
            toType = OperandType.DOUBLE;
            break;
        case L2I:
            fromType = OperandType.LONG;
            toType = OperandType.INTEGER;
            break;
        case L2F:
            fromType = OperandType.LONG;
            toType = OperandType.FLOAT;
            break;
        case L2D:
            fromType = OperandType.LONG;
            toType = OperandType.DOUBLE;
            break;
        case F2I:
            fromType = OperandType.FLOAT;
            toType = OperandType.INTEGER;
            break;
        case F2L:
            fromType = OperandType.FLOAT;
            toType = OperandType.LONG;
            break;
        case F2D:
            fromType = OperandType.FLOAT;
            toType = OperandType.DOUBLE;
            break;
        case D2I:
            fromType = OperandType.DOUBLE;
            toType = OperandType.INTEGER;
            break;
        case D2L:
            fromType = OperandType.DOUBLE;
            toType = OperandType.LONG;
            break;
        case D2F:
            fromType = OperandType.DOUBLE;
            toType = OperandType.FLOAT;
            break;
        case I2B:
            fromType = OperandType.INTEGER;
            toType = OperandType.BYTE;
            break;
        case I2C:
            fromType = OperandType.INTEGER;
            toType = OperandType.CHAR;
            break;
        case I2S:
            fromType = OperandType.INTEGER;
            toType = OperandType.SHORT;
            break;
        default:
            assert (false) : "Unhandled typecast opcode";
        }

        return new Pair<OpCode, Integer>(new TypeCast(fromType, toType), 0);
    }

    /**
     * Handles opcodes of comparision operations ([0x94..0x97]) from a (java)
     * bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> compareOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {

        OperandType t = null;
        //boolean naNGreater = false;
        switch (opc) {
        case LCMP:
            t = OperandType.LONG;
            break;
        case FCMPG:
        case FCMPL:
            // we currently do not do float comparisons, so these behave the same
            t = OperandType.FLOAT;
            break;
        case DCMPG:
        case DCMPL:
            // we currently do not do double comparisons, so these behave the same
            t = OperandType.DOUBLE;
            break;
        default:
            assert (false) : "Unhandled opcode!";
        }

        return new Pair<OpCode, Integer>(new Cmp(t), 0);
    }

    /**
     * Handles opcodes of branch operations ([0x99,0xa8],[0xc6,0xc7]) from a
     * (java) bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> branchOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;
        Integer operandBytes = 0;
        int branchOffset = (int) getSignedFromByteArray(methodBytecode, position + 1, 2);
        operandBytes = 2;
        ComparisonType cond = null;
        OperandType type = null;
        boolean cmp = false;
        boolean subroutine = false;

        if (opc <= IF_ACMPNE) {
            switch ((opc - IFEQ) % 6) {
            case 0:
                cond = ComparisonType.EQ;
                break;
            case 1:
                cond = ComparisonType.NE;
                break;
            case 2:
                cond = ComparisonType.LT;
                break;
            case 3:
                cond = ComparisonType.GE;
                break;
            case 4:
                cond = ComparisonType.GT;
                break;
            case 5:
                cond = ComparisonType.LE;
                break;
            default:
                assert (false) : "Unhandled opcode";
            }

            if (opc <= IFLE) {
                type = OperandType.INTEGER;
                cmp = false;
            } else if (opc <= IF_ICMPLE) {
                type = OperandType.INTEGER;
                cmp = true;
            } else {
                type = OperandType.ADDRESS;
                cmp = true;
            }

        } else if (opc == GOTO) {
            cond = ComparisonType.JMP;
        } else if (opc == JSR) {
            branchOffset = (int) getSignedFromByteArray(methodBytecode, position + 1, 2);
            cond = ComparisonType.JMP;
            subroutine = true;
            operandBytes = 2;
        } else if (opc == IFNULL) {
            cond = ComparisonType.NULL;
            type = OperandType.ADDRESS;
        } else if (opc == IFNONNULL) {
            cond = ComparisonType.NONNULL;
            type = OperandType.ADDRESS;
        } else if (opc == GOTO_W) {
            cond = ComparisonType.JMP;
            branchOffset = (int) getSignedFromByteArray(methodBytecode, position + 1, 4);
            operandBytes = 4;
        } else if (opc == JSR_W) {
            cond = ComparisonType.JMP;
            subroutine = true;
            branchOffset = (int) getSignedFromByteArray(methodBytecode, position + 1, 4);
            operandBytes = 4;
        }
        currentOpCode = new Branch(branchOffset, cmp, cond, type, subroutine);

        return new Pair<OpCode, Integer>(currentOpCode, operandBytes);
    }

    /**
     * Handles opcodes of switch tables (0xaa,0xab) from a (java) bytecode
     * file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> switchOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;
        int operandBytes = 0;

        if (opc == TABLESWITCH) {
            final int padding = (4 - (position + 1) % 4) % 4;

            final int low = (int) getUSignedFromByteArray(methodBytecode, position + padding + 4 + 1, 4);
            final int high = (int) getUSignedFromByteArray(methodBytecode, position + padding + 8 + 1, 4);
            currentOpCode = new TableSwitch(high, low);

            operandBytes = padding + 12 + 4 * (high - low + 1);

        } else if (opc == LOOKUPSWITCH) {
            final int padding = (4 - (position + 1) % 4) % 4;
            final int npairs = (int) getUSignedFromByteArray(methodBytecode, position + padding + 5, 4);
            currentOpCode = new LookupSwitch(position, npairs);
            operandBytes = padding + 8 + npairs * 8;
        }
        return new Pair<OpCode, Integer>(currentOpCode, operandBytes);
    }

    /**
     * Handles opcodes of return operations ([0xac,0xb1]) from a (java) bytecode
     * file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> returnOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;

        switch (opc - IRETURN) {
        case 0:
            currentOpCode = new Return(OperandType.INTEGER);
            break;
        case 1:
            currentOpCode = new Return(OperandType.LONG);
            break;
        case 2:
            currentOpCode = new Return(OperandType.FLOAT);
            break;
        case 3:
            currentOpCode = new Return(OperandType.DOUBLE);
            break;
        case 4:
            currentOpCode = new Return(OperandType.ADDRESS);
            break;
        case 5:
            currentOpCode = new Return(null);
            break;
        default:
            assert (false) : "Unhandled opcode!";
        }

        return new Pair<OpCode, Integer>(currentOpCode, 0);
    }

    /**
     * Handles opcodes of field access operations ([0xb2,0xb5]) from a (java)
     * bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> fieldAccessOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;

        final int fieldIdx = (int) getUSignedFromByteArray(methodBytecode, position + 1, 2);
        final CPFieldRef fieldRef = (CPFieldRef) this.classFile.getConstant(fieldIdx);
        final ClassName classN = this.classFile.resolveClassNameRef(fieldRef.getClassIndex());
        final CPNameAndTypeRef fieldNameAndType =
            (CPNameAndTypeRef) this.classFile.getConstant(fieldRef.getNameAndTypeRefIndex());
        final String fieldNameAndDescriptor = this.classFile.resolveStringRef(fieldNameAndType.getNameRefIndex());

        final FieldIdentifier fieldId = new FieldIdentifier(classN, fieldNameAndDescriptor);
        FieldAccessType type = null;
        FieldAccessRW rw = null;

        switch (opc - GETSTATIC) {
        case 0:
            type = FieldAccessType.STATIC;
            rw = FieldAccessRW.READ;
            break;
        case 1:
            type = FieldAccessType.STATIC;
            rw = FieldAccessRW.WRITE;
            break;
        case 2:
            type = FieldAccessType.INSTANCE;
            rw = FieldAccessRW.READ;
            break;
        case 3:
            type = FieldAccessType.INSTANCE;
            rw = FieldAccessRW.WRITE;
            break;
        default:
            assert (false) : "Unhandled opcode!";
        }
        currentOpCode = new FieldAccess(fieldId, type, rw);

        return new Pair<OpCode, Integer>(currentOpCode, 2);
    }

    /**
     * Handles opcodes of method invocations ([0xb6,0xb9]) from a (java)
     * bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> invocationOpCodes(final byte[] methodBytecode, final int position, final int opc) {
        final int index = (int) getUSignedFromByteArray(methodBytecode, position + 1, 2);

        int operandBytes;
        if (opc == INVOKEINTERFACE) {
            operandBytes = 4;
            /*
             * 3th byte contains number of arguments (which is redundant and
             * can be derived from the descriptor)
             * 4th byte is always 0 for historical reasons
             */
        } else {
            operandBytes = 2;
        }

        InvocationType invType = null;
        switch (opc) {
        case INVOKEVIRTUAL:
            invType = InvocationType.VIRTUAL;
            break;
        case INVOKESPECIAL:
            invType = InvocationType.SPECIAL;
            break;
        case INVOKESTATIC:
            invType = InvocationType.STATIC;
            break;
        case INVOKEINTERFACE:
            invType = InvocationType.INTERFACE;
            break;
        case INVOKEDYNAMIC: {
            InvokeDynamic res = parseInvokeDynamic(index);
            return new Pair<>(res, 4);
        }
        default:
            assert (false) : "Unhandled opcode!";
        }

        // Now get all data from the constant pool:
        final ClassName classN;
        final int methodNameAndTypeRefIndex;
        if (invType != InvocationType.INTERFACE) {
            final CpMemberRef methodRef = (CpMemberRef) this.classFile.getConstant(index);
            final FuzzyType fuzzy = this.classFile.resolveClassNameRefFuzzy(methodRef.getClassIndex());
            if (fuzzy.getArrayDimension() != 0) {
                classN = ClassName.Important.JAVA_LANG_OBJECT.getClassName();
            } else {
                classN = ((FuzzyClassType) fuzzy).getMinimalClass();
            }
            methodNameAndTypeRefIndex = methodRef.getNameAndTypeRefIndex();
        } else {
            final CpMemberRef methodRef = (CpMemberRef) this.classFile.getConstant(index);
            classN = this.classFile.resolveClassNameRef(methodRef.getClassIndex());
            methodNameAndTypeRefIndex = methodRef.getNameAndTypeRefIndex();
        }
        final CPNameAndTypeRef methodNameAndTypeRef =
            (CPNameAndTypeRef) this.classFile.getConstant(methodNameAndTypeRefIndex);
        final String methodName = this.classFile.resolveStringRef(methodNameAndTypeRef.getNameRefIndex());
        final String methodType = this.classFile.resolveStringRef(methodNameAndTypeRef.getDescriptorRefIndex());
        final MethodIdentifier methodId =
            new MethodIdentifier(classN, methodName, new ParsedMethodDescriptor(methodType));

        final OpCode currentOpCode = new InvokeMethod(invType, methodId);
        return new Pair<OpCode, Integer>(currentOpCode, operandBytes);
    }

    private InvokeDynamic parseInvokeDynamic(final int index) {
        CPInvokeDynamic invokeDynamic = (CPInvokeDynamic) this.classFile.getConstant(index);
        BootstrapMethod bootstrapMethod =
                this.classFile.getBootstrapMethods().get(invokeDynamic.getBootstrapMethodAttrIndex());
        List<Short> bootstrapArguments = bootstrapMethod.getBootstrapArguments();
        // currently (2017) it seems like javac exclusively generates bootstrap methods with three or five arguments...
        assert Arrays.asList(3, 5).contains(bootstrapArguments.size()) :
            "bootstrap method with " + bootstrapArguments.size() + " arguments in class " + this.getClassName();
        // ... where the second argument always points to the implementation that is eventually invoked by the
        // dynamically created implementation of the functional interface
        short methodHandleIndex = bootstrapArguments.get(1);
        CPMethodHandle methodHandle = (CPMethodHandle) this.classFile.getConstant(methodHandleIndex);
        int invocationType = methodHandle.getReferenceKind();
        CpMemberRef methodRef = (CpMemberRef) this.classFile.getConstant(methodHandle.getReferenceIndex());
        ClassName classN = this.classFile.resolveClassNameRef(methodRef.getClassIndex());
        CPNameAndTypeRef methodNameAndTypeRef =
                (CPNameAndTypeRef) this.classFile.getConstant(methodRef.getNameAndTypeRefIndex());
        String methodName = this.classFile.resolveStringRef(methodNameAndTypeRef.getNameRefIndex());
        String methodType = this.classFile.resolveStringRef(methodNameAndTypeRef.getDescriptorRefIndex());
        MethodIdentifier resolvedMethodId =
                new MethodIdentifier(classN, methodName, new ParsedMethodDescriptor(methodType));
        int functionalInterfaceNameAndFactoryTypeIndex = invokeDynamic.getNameAndTypeIndex();
        CPNameAndTypeRef functionalInterfaceNameAndFactoryType =
                (CPNameAndTypeRef) this.classFile.getConstant(functionalInterfaceNameAndFactoryTypeIndex);
        String functionalInterfaceFactoryMethodDescriptorStr =
                this.classFile.resolveStringRef(functionalInterfaceNameAndFactoryType.getDescriptorRefIndex());
        ParsedMethodDescriptor functionalInterfaceFactoryMethodDescriptor =
                new ParsedMethodDescriptor(functionalInterfaceFactoryMethodDescriptorStr);
        ClassName functionalInterface =
                ((FuzzyClassType) functionalInterfaceFactoryMethodDescriptor.getReturnType()).getMinimalClass();
        // the arguments of the functionalInterfaceFactory (i.e., the method that creates an implementation of the
        // functional interface at runtime) are exactly the captured arguments (i.e., the closure) which will later
        // become members of the dynamically created class
        List<FuzzyType> capturedArguments =
                new ArrayList<FuzzyType>(functionalInterfaceFactoryMethodDescriptor.getArgumentCount());
        for (int i = 0; i < functionalInterfaceFactoryMethodDescriptor.getArgumentCount(); i++) {
            capturedArguments.add(i,functionalInterfaceFactoryMethodDescriptor.getType(i));
        }
        InvokeDynamic res = new InvokeDynamic(resolvedMethodId, functionalInterface, invocationType, capturedArguments);
        return res;
    }

    /**
     * Handles opcodes for array handling ([0xbc,0xbe], 0xc5) from a (java)
     * bytecode file.
     *
     * @param methodBytecode
     *            the full bytecode array
     * @param position
     *            current position in the bytecode
     * @param opc
     *            number of the currently worked on opcode
     * @param wide
     *            indicates whether this opcode was prefixed by the behaviour-changing
     *            wide opcode
     * @return a Pair with the resulting opcode and the number of used up bytes
     */
    private Pair<OpCode, Integer> arrayOpCodes(
        final byte[] methodBytecode,
        final int position,
        final int opc,
        final boolean wide)
    {
        OpCode currentOpCode = null;
        int operandBytes;

        if (opc == NEWARRAY) {
            operandBytes = 1; // just the type
            String t = null;
            switch ((int) getUSignedFromByteArray(methodBytecode, position + 1, 1)) {
            case 4:
                // boolean
                t = "[Z";
                break;
            case 5:
                t = "[C";
                break;
            case 6:
                t = "[F";
                break;
            case 7:
                t = "[D";
                break;
            case 8:
                t = "[B";
                break;
            case 9:
                t = "[S";
                break;
            case 10:
                t = "[I";
                break;
            case 11:
                // long
                t = "[J";
                break;
            default:
                assert (false) : "Unhandled array type!";
            }
            currentOpCode = new ArrayCreate(FuzzyType.parseTypeDescriptor(t), 1, false);
        } else if (opc == ANEWARRAY || opc == MULTIANEWARRAY) {
            assert (!wide) : "wide opcode used together with (multi)anewarray, semantics unknown";
            final int index = (int) getUSignedFromByteArray(methodBytecode, position + 1, 2);

            final int typeDescriptionIndex = ((CPClassRef) this.classFile.getConstant(index)).getClassRefIndex();
            final CPString typeDescription = (CPString) this.classFile.getConstant(typeDescriptionIndex);
            final FuzzyType type = FuzzyType.parseType(typeDescription.getString());

            if (opc == MULTIANEWARRAY) {
                // two bytes for the type, one for the dimensions
                operandBytes = 3;

                /* | The runtime constant pool item at the index must be a
                 * | symbolic reference to a class, array, or interface type. The
                 * | named class, array, or interface type is resolved (�5.4.3.1).
                 * | The resulting entry must be an array class type of dimensionality
                 * | greater than or equal to dimensions.
                 *   -- JVMS
                 */

                final int dimensions = (int) getUSignedFromByteArray(methodBytecode, position + 3, 1);

                assert (type.getArrayDimension() >= dimensions);
                currentOpCode = new ArrayCreate(type, dimensions, true);
            } else {
                // two bytes for the type
                operandBytes = 2;

                /* | The runtime constant pool item at that index must be a
                 * | symbolic reference to a class, array, or interface type.
                 * | The named class, array, or interface type is resolved
                 * | (�5.4.3.1). A new array with components of that type ...
                 */

                currentOpCode = new ArrayCreate(type.getEnclosingType(), 1, false);
            }
        } else if (opc == ARRAYLENGTH) {
            currentOpCode = new ArrayLength();
            operandBytes = 0;
        } else {
            assert (false);
            operandBytes = -1;
        }
        return new Pair<OpCode, Integer>(currentOpCode, operandBytes);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getLocalMethod(java.lang.String, aprove.verification.oldframework.Bytecode.Parser.ParsedMethodDescriptor)
     */
    @Override
    public ParsedMethod getLocalMethod(final String methodName, final ParsedMethodDescriptor callDescriptor) {
        final Map<ParsedMethodDescriptor, ParsedMethod> methods = this.methodMap.get(methodName);
        if (methods == null) {
            return null;
        }
        return methods.get(callDescriptor);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getLocalMethod(aprove.verification.oldframework.Bytecode.Parser.MethodIdentifier)
     */
    @Override
    public ParsedMethod getLocalMethod(final MethodIdentifier id) {
        return this.getLocalMethod(id.getMethodName(), id.getDescriptor());
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getClassPath()
     */
    @Override
    public ClassPath getClassPath() {
        return this.classPath;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getSuperType()
     */
    @Override
    public TypeTree getSuperType() {
        return this.typeTree.getSuperType();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getMethods()
     */
    @Override
    public Collection<IMethod> getMethods() {
        final Collection<IMethod> result = new LinkedHashSet<IMethod>();
        for (final Map<ParsedMethodDescriptor, ParsedMethod> map : this.methodMap.values()) {
            result.addAll(map.values());
        }
        return result;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getType()
     */
    @Override
    public TypeTree getType() {
        return this.typeTree;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.className == null) ? 0 : this.className.hashCode());
        result = prime * result + ((this.instanceFields == null) ? 0 : this.instanceFields.hashCode());
        result = prime * result + ((this.methodMap == null) ? 0 : this.methodMap.hashCode());
        result = prime * result + ((this.staticFields == null) ? 0 : this.staticFields.hashCode());
        result = prime * result + ((this.typeTree == null) ? 0 : this.typeTree.hashCode());
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ParsedClass other = (ParsedClass) obj;
        if (this.classFile == null) {
            if (other.classFile != null) {
                return false;
            }
        } else if (!this.classFile.equals(other.classFile)) {
            return false;
        }
        if (this.className == null) {
            if (other.className != null) {
                return false;
            }
        } else if (!this.className.equals(other.className)) {
            return false;
        }
        if (this.instanceFields == null) {
            if (other.instanceFields != null) {
                return false;
            }
        } else if (!this.instanceFields.equals(other.instanceFields)) {
            return false;
        }
        if (this.methodMap == null) {
            if (other.methodMap != null) {
                return false;
            }
        } else if (!this.methodMap.equals(other.methodMap)) {
            return false;
        }
        if (this.classPath == null) {
            if (other.classPath != null) {
                return false;
            }
        } else if (!this.classPath.equals(other.classPath)) {
            return false;
        }
        if (this.staticFields == null) {
            if (other.staticFields != null) {
                return false;
            }
        } else if (!this.staticFields.equals(other.staticFields)) {
            return false;
        }
        if (this.typeTree == null) {
            if (other.typeTree != null) {
                return false;
            }
        } else if (!this.typeTree.equals(other.typeTree)) {
            return false;
        }
        return true;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getMethodRecursively(aprove.verification.oldframework.Bytecode.Parser.MethodIdentifier)
     */
    @Override
    public IMethod getMethodRecursively(final MethodIdentifier resolvedMethodId) {
        IClass currentClass = this;

        while (currentClass != null) {
            final IMethod methodCandidate = currentClass.getLocalMethod(resolvedMethodId);
            if (methodCandidate != null) {
                return methodCandidate;
            }

            //Couldn't find method in this class, travel the type tree upwards:
            final TypeTree superTypeTree = currentClass.getSuperType();
            if (superTypeTree == null) {
                //We have no super type, so we are probably Object:
                break;
            }
            currentClass = this.classPath.getClass(currentClass.getSuperType().getClassName());
        }

        return null;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getStaticFields()
     */
    @Override
    public ImmutableMap<String, Field> getStaticFields() {
        return this.staticFields;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getInstanceFields()
     */
    @Override
    public ImmutableMap<String, Field> getInstanceFields() {
        return this.instanceFields;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getField(java.lang.String)
     */
    @Override
    public Field getField(final String fieldNameAndDescriptor) {
        Field result = this.instanceFields.get(fieldNameAndDescriptor);
        if (result == null) {
            result = this.staticFields.get(fieldNameAndDescriptor);
        }
        return result;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#isFinal()
     */
    @Override
    public boolean isFinal() {
        return this.classFile.isFinal();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#isEffectivelyFinal()
     */
    @Override
    public boolean isEffectivelyFinal() {
        return this.isFinal()
            || (!this.typeTree.hasSubTypes() && this.typeTree.getImplementingTypes().isEmpty());

    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IParsedClass#getClassFileVersion()
     */
    @Override
    public Pair<Integer, Integer> getClassFileVersion() {
        return this.classFile.getClassFileVersion();
    }
}
