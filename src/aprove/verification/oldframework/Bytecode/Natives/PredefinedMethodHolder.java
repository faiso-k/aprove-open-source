package aprove.verification.oldframework.Bytecode.Natives;

import java.io.*;
import java.util.*;
import java.util.stream.*;

import org.json.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.MethodSummary.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author ffrohn
 *
 * class holding representations of predefined (i.e., native or overwritten) methods
 *
 */
public final class PredefinedMethodHolder {

    private JBCOptions options;

    /**
     * Mapping of method identifiers to native pre-defined methods.
     */
    private HashMap<MethodIdentifier, PredefinedMethod> nativeMethods;

    /**
     * Mapping of method identifiers to pre-defined methods for methods that
     * are usually implemented non-natively.
     */
    private HashMap<MethodIdentifier, PredefinedMethod> overwrittenMethods;

    public PredefinedMethodHolder(JBCOptions options) {
        this.options = options;
        this.initialize();
    }

    /**
     * @param name The name of the method to look for
     * @return The native method, if any is found for the given name, null otherwise
     */
    public PredefinedMethod getNativeMethod(final MethodIdentifier name) {
        if (options.loadAllNativeMethods()
            && "registerNatives".equals(name.getMethodName())
            && "()V".equals(name.getDescriptor().toString())
            && (name.getClassName().getPkgName().startsWith("java/") || (name.getClassName().getPkgName().startsWith("sun/")))) {
            return new NativeNop(0);
        }
        return this.nativeMethods.get(name);
    }

    public void forceOverwriteWithDefaultSummary(IMethod pm, HandlingMode goal, String reason) {
        overwriteMethod(pm.getMethodIdentifier(), MethodSummary.defaultSummary(pm, goal, reason));
    }

    public boolean overwriteWithDefaultSummary(IMethod pm, HandlingMode goal, String reason) {
        overwriteMethod(pm.getMethodIdentifier(), MethodSummary.defaultSummary(pm, goal, reason));
        return true;
    }

    /**
     * @param name The name of the method to look for
     * @return The native method, if any is found for the given name, null otherwise
     */
    public PredefinedMethod getOverwritingMethod(IMethod pm, State s) {
        ClassPath cp = s.getClassPath();
        if (this.overwrittenMethods.containsKey(pm.getMethodIdentifier())) {
            IClass pc = pm.getIClass();
            MethodIdentifier mid = pm.getMethodIdentifier();
            while (true) {
                mid = new MethodIdentifier(pc.getClassName(), mid.getMethodName(), mid.getDescriptor());
                if (this.overwrittenMethods.containsKey(mid)) {
                    PredefinedMethod pdm = this.overwrittenMethods.get(mid);
                    if (pdm.isApplicable(s)) {
                        return pdm;
                    } else {
                        break;
                    }
                }
                if (pc.getSuperType() == null) {
                    break;
                } else {
                    pc = cp.getClass(pc.getSuperType().getClassName());
                }
            }
        }
        if (options.summarizeAllMethodCalls()) {
            overwriteWithDefaultSummary(pm, s.getTerminationGraph().getGoal(), "method call");
        } else {
            boolean isLibraryCall = pm.getIClass().getClassStreamProviderType() == ClassStreamProvider.Type.Library;
            if (isLibraryCall && options.summarizeAllLibraryCalls()) {
                overwriteWithDefaultSummary(pm, s.getTerminationGraph().getGoal(), "library call");
            }
        }
        return null;
    }

    /**
     * @param name The name of the method to register
     * @param method The implementation of that method
     */
    public void registerNativeMethod(final MethodIdentifier name, final PredefinedMethod method) {
        this.nativeMethods.put(name, method);
    }

    /**
     * @see PredefinedMethodHolder#registerNativeMethod(MethodIdentifier, PredefinedMethod)
     * @param cName Fully qualified name of the class the method belongs to;
     * package and class name separator is "."
     * @param mName Method name
     * @param descriptor Method descriptor
     * @param method Implementation
     */
    public void registerNativeMethod(final String cName,
        final String mName,
        final String descriptor,
        final PredefinedMethod method) {
        this.registerNativeMethod(
            new MethodIdentifier(ClassName.fromDotted(cName), mName, new ParsedMethodDescriptor(descriptor)), method);
    }

    /**
     * @param name The id of the method to override
     * @param method The implementation of that method
     */
    public void overwriteMethod(final MethodIdentifier name, final PredefinedMethod method) {
        this.overwrittenMethods.put(name, method);
    }

    /**
     * @see PredefinedMethodHolder#overwriteMethod(MethodIdentifier, PredefinedMethod)
     * @param cName Fully qualified name of the class the method belongs to;
     * package and class name separator is "."
     * @param mName Method name
     * @param descriptor Method descriptor
     * @param method Implementation
     */
    public void overwriteMethod(final String cName,
        final String mName,
        final String descriptor,
        final PredefinedMethod method) {
        this.overwriteMethod(
            new MethodIdentifier(ClassName.fromDotted(cName), mName, new ParsedMethodDescriptor(descriptor)), method);
    }

    /**
     * @param mId some method id
     * @return true iff we have overriden the Java implementation.
     */
    public boolean hasOverridingMethod(IMethod pm, State s) {
        return getOverwritingMethod(pm, s) != null;
    }

    /**
     * @param mId some method id
     * @param s check if the overriding method is applicable in s
     * @return true iff we have overriden the Java implementation, and the overriding method is applicable in s
     */
    public boolean isOverriden(IMethod pm, State s) {
        PredefinedMethod m = getOverwritingMethod(pm, s);
        return m != null && m.isApplicable(s);
    }

    /**
     * called during the construction of the object for initialization
     */
    private void initialize() {
        this.nativeMethods = new LinkedHashMap<>();
        this.overwrittenMethods = new LinkedHashMap<>();
        this.registerNativeMethod("java.lang.Throwable", "fillInStackTrace", "()Ljava/lang/Throwable;", new NativeNop(0));
        if (options.loadAllNativeMethods()) {
            this.registerNativeMethod("java.lang.Throwable", "fillInStackTrace", "(I)Ljava/lang/Throwable;", new NativeNop(1));
            this.registerNativeMethod("java.lang.Object", "hashCode", "()I",
                new ConstantIntReturn(AbstractInt.getUnknown(IntegerType.UNBOUND), OperandType.INTEGER, 1));
            this.registerNativeMethod("java.lang.Throwable", "getStackTraceDepth", "()I",
                new ConstantIntReturn(AbstractInt.getZero(), OperandType.INTEGER, 1));
            this.registerNativeMethod("java.lang.String", "intern", "()Ljava/lang/String;", new FreshStringReturn(1, true));
            this.registerNativeMethod(
                "java.lang.System",
                "currentTimeMillis",
                "()J",
                new ConstantIntReturn(AbstractInt.create(IntervalBound.ONE,
                    IntegerType.UNBOUND.getUpper(),
                    false,
                    IntervalBound.ONE,
                    IntegerType.UNBOUND.getUpper(),
                    0,
                    0),
                    OperandType.LONG, 0));
            this.registerNativeMethod("java.lang.Object", "getClass", "()Ljava/lang/Class;", new GetClass());
            this.registerNativeMethod("java.lang.Class", "getPrimitiveClass", "(Ljava/lang/String;)Ljava/lang/Class;",
                new GetPrimitiveClass());
            this.registerNativeMethod("java.lang.Class", "getClassLoader0", "()Ljava/lang/ClassLoader;", new GetClassLoader());
            this.registerNativeMethod("java.lang.Class", "desiredAssertionStatus0", "(Ljava/lang/Class;)Z",
                new ConstantIntReturn(AbstractInt.getUnknown(IntegerType.JAVA_INT), OperandType.INTEGER, 1));
            this.registerNativeMethod("java.lang.Class", "getName0", "()Ljava/lang/String;", new FreshStringReturn(1, true));
            this.registerNativeMethod("java.lang.Float", "floatToRawIntBits", "(F)I",
                new ConstantIntReturn(AbstractInt.getUnknown(IntegerType.JAVA_INT), OperandType.INTEGER, 1));
            this.registerNativeMethod("java.lang.System", "arraycopy", "(Ljava/lang/Object;ILjava/lang/Object;II)V",
                new SystemArrayCopy());
            this.registerNativeMethod("java.lang.Double", "doubleToRawLongBits", "(D)J",
                new ConstantIntReturn(AbstractInt.getUnknown(IntegerType.JAVA_INT), OperandType.LONG, 1));
            this.registerNativeMethod("java.lang.System", "initProperties", "(Ljava/util/Properties;)Ljava/util/Properties;",
                new InitProperties());
            this.registerNativeMethod("java.lang.System", "setIn0", "(Ljava/io/InputStream;)V", new JLSystemSetStream("in"));
            this.registerNativeMethod("java.lang.System", "setOut0", "(Ljava/io/PrintStream;)V", new JLSystemSetStream("out"));
            this.registerNativeMethod("java.lang.System", "setErr0", "(Ljava/io/PrintStream;)V", new JLSystemSetStream("err"));
            this.registerNativeMethod("sun.reflect.Reflection", "getCallerClass", "(I)Ljava/lang/Class;", new GetCallerClass());
            this.registerNativeMethod("java.io.FileInputStream", "initIDs", "()V", new NativeNop(0));
            this.registerNativeMethod("java.io.FileDescriptor", "initIDs", "()V", new NativeNop(0));
            this.registerNativeMethod("java.io.FileOutputStream", "initIDs", "()V", new NativeNop(0));
            this.registerNativeMethod("java.lang.System", "nanoTime", "()J",
                    new ConstantIntReturn(AbstractInt.getUnknown(IntegerType.JAVA_LONG), OperandType.LONG, 0));
            this.registerNativeMethod("java.lang.System", "identityHashCode", "(Ljava/lang/Object;)I",
                    new ConstantIntReturn(AbstractInt.getUnknown(IntegerType.JAVA_INT), OperandType.INTEGER, 1));

            this.overwriteMethod("java.lang.System", "getProperty", "(Ljava/lang/String;)Ljava/lang/String;",
                new FreshStringReturn(1, false));
            this.overwriteMethod("java.lang.System", "setProperty",
                "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;", new FreshStringReturn(2, false));
            this.overwriteMethod("java.util.concurrent.atomic.AtomicInteger", "compareAndSet", "(II)Z", new AtomicIntSet(3,
                0, true));
            this.overwriteMethod("java.util.concurrent.atomic.AtomicInteger", "weakCompareAndSet", "(II)Z",
                new AtomicIntSet(3, 0, true));
            this.overwriteMethod("java.util.concurrent.atomic.AtomicInteger", "lazySet", "(I)V", new AtomicIntSet(2, 0,
                false));
            this.overwriteMethod("java.util.concurrent.atomic.AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl",
                "<init>", "(Ljava/lang/Class;Ljava/lang/Class;Ljava/lang/String;)V",
                new AtomicReferenceFieldUpdaterImplInit());
            this.overwriteMethod("java.util.concurrent.atomic.AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl",
                "compareAndSet", "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Z",
                new AtomicReferenceFieldSet(4, 3, 0, true));
            this.overwriteMethod("java.util.concurrent.atomic.AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl",
                "weakCompareAndSet", "(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Z",
                new AtomicReferenceFieldSet(4, 3, 0, true));
            this.overwriteMethod("java.util.concurrent.atomic.AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl",
                "set", "(Ljava/lang/Object;Ljava/lang/Object;)V", new AtomicReferenceFieldSet(3, 2, 0, true));
            this.overwriteMethod("java.util.concurrent.atomic.AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl",
                "lazySet", "(Ljava/lang/Object;Ljava/lang/Object;)V", new AtomicReferenceFieldSet(3, 2, 0, true));
            this.overwriteMethod("java.util.concurrent.atomic.AtomicReferenceFieldUpdater$AtomicReferenceFieldUpdaterImpl",
                "get", "(Ljava/lang/Object;)Ljava/lang/Object;", new AtomicReferenceFieldGet());

            this.overwriteMethod("java.lang.String", "length", "()I", new StringLength());
            this.overwriteMethod("java.lang.String", "charAt", "(I)C", new StringCharAt());
            this.overwriteMethod("java.lang.String", "equals", "(Ljava/lang/Object;)Z", new StringEquals());

            this.overwriteMethod("java.lang.String", "<init>", "([BLjava/nio/charset/Charset;)V", new StringInit(2, 1));
            this.overwriteMethod("java.lang.String", "<init>", "([BIILjava/lang/String;)V", new StringInit(4, 3));
            this.overwriteMethod("java.lang.String", "<init>", "([BIILjava/nio/charset/Charset;)V", new StringInit(4, 3));
            this.overwriteMethod("java.lang.String", "<init>", "([BLjava/lang/String;)V", new StringInit(2, 0));
            this.overwriteMethod("java.lang.String", "<init>", "([BII)V", new StringInit(3, 2));
            this.overwriteMethod("java.lang.String", "<init>", "([B)V", new StringInit(1, 0));
            this.overwriteMethod("java.lang.String", "<init>", "([C)V", new StringInit(1, 0));
            this.overwriteMethod("java.lang.String", "<init>", "([CII)V", new StringInit(3, 2));
            this.overwriteMethod("java.lang.String", "<init>", "([III)V", new StringInit(3, 2));
            this.overwriteMethod("java.lang.String", "<init>", "([BIII)V", new StringInit(4, 3));
            this.overwriteMethod("java.lang.String", "<init>", "([BI)V", new StringInit(2, 1));
            this.overwriteMethod("java.lang.String", "<init>", "(Ljava/lang/StringBuilder;)V", new StringInit(1, 0));
            this.overwriteMethod("java.lang.String", "<init>", "(Ljava/lang/StringBuffer;)V", new StringInit(1, 0));
            this.overwriteMethod("java.lang.System", "exit", "(I)V", new SystemExit());
            this.registerNativeMethod("java.lang.Integer", "parseInt", "(Ljava/lang/String;)I",
                    new ConstantIntReturn(AbstractInt.getUnknown(IntegerType.JAVA_INT), OperandType.INTEGER, 1));
        }
    }

    public void load(String filename) throws FileNotFoundException {
        for (Pair<MethodSummary, List<String>> summary : JSONUtil.loadFromJSON(filename)) {
            this.overwriteMethod(summary.x.getMethodIdentifier(), summary.x);
        }
    }

    public void dumpDefaultSummaries() {
        try {
            File summaries = File.createTempFile("summaries", ".json");
            summaries.createNewFile();
            BufferedWriter writer = new BufferedWriter(new FileWriter(summaries));

            JSONObject res = JSONUtil.storeAsJSON(overwrittenMethods.values().stream()
                                                                    .filter(pm -> pm instanceof MethodSummary)
                                                                    .map(MethodSummary.class::cast)
                                                                    .filter(MethodSummary::isDefaultSummary)
                                                                    .collect(Collectors.toList())
                    );
            writer.write(res.toString(4));

            System.err.println("dumped overwritten methods to " + summaries.getAbsolutePath());
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

}
