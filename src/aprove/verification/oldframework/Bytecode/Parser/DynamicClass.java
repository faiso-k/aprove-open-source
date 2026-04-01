package aprove.verification.oldframework.Bytecode.Parser;

import static aprove.verification.oldframework.Bytecode.Parser.ClassFileParserConstants.*;
import static java.util.Collections.*;

import java.util.*;
import java.util.concurrent.atomic.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.OpCodes.InvokeMethod.*;
import aprove.verification.oldframework.Bytecode.Parser.Attributes.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ClassStreamProvider.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class DynamicClass implements IClass {

    private static AtomicInteger count = new AtomicInteger();
    private ClassName className;
    private IMethod method;
    private ClassStreamProvider.Type classStreamProviderType;
    private ClassPath cPath;
    private IClass functionalInterface;
    private TypeTree type;
    private Map<String, Field> instanceFields = new LinkedHashMap<>();

    public DynamicClass(IClass callingClass, IClass functionalInterface, List<FuzzyType> args, IMethod lambdaImpl, InvocationType invocationType) {
        this.classStreamProviderType = callingClass.getClassStreamProviderType();
        this.cPath = callingClass.getClassPath();
        this.className = ClassName.fromSlashed(callingClass.getClassName().getPkgName() + "/$$Lambda$" + count.incrementAndGet());
        this.functionalInterface = functionalInterface;
        int i = 0;
        for (FuzzyType a: args) {
            String name = InvokeDynamic.getArgName(i);
            i++;
            Field f = new Field(className, FIELD_ACCESS_FLAG_PRIVATE & FIELD_ACCESS_FLAG_FINAL, name, a.getTypeDescriptor(), new Attribute[0], null);
            instanceFields.put(name, f);
        }
        this.method = new DynamicMethod(lambdaImpl, this, functionalInterface, invocationType);
        String signature = method.getName() + method.getDescriptor();
        int accessFlags = METHOD_ACCESS_FLAG_PUBLIC;
        TypeTree interfaceType = cPath.getTypeTree(functionalInterface.getClassName());
        this.type = new TypeTree(className,
                getSuperType(),
                singletonList(interfaceType),
                false,
                false,
                false,
                true,
                singletonMap(signature, accessFlags));
    }

    @Override
    public Type getClassStreamProviderType() {
        return classStreamProviderType;
    }

    @Override
    public ClassName getClassName() {
        return className;
    }

    @Override
    public IMethod getLocalMethod(String methodName, ParsedMethodDescriptor callDescriptor) {
        if (methodName.equals(method.getName()) && callDescriptor.equals(method.getDescriptor())) {
            return method;
        } else {
            return null;
        }
    }

    @Override
    public IMethod getLocalMethod(MethodIdentifier id) {
        return getLocalMethod(id.getMethodName(), id.getDescriptor());
    }

    @Override
    public ClassPath getClassPath() {
        return cPath;
    }

    @Override
    public TypeTree getSuperType() {
        return cPath.getTypeTree(Important.JAVA_LANG_OBJECT.getClassName());
    }

    @Override
    public Collection<IMethod> getMethods() {
        return singleton(method);
    }

    @Override
    public TypeTree getType() {
        return this.type;
    }

    @Override
    public IMethod getMethodRecursively(MethodIdentifier resolvedMethodId) {
        IMethod res = getLocalMethod(resolvedMethodId);
        if (res == null) {
            res = cPath.getClass(Important.JAVA_LANG_OBJECT.getClassName()).getMethodRecursively(resolvedMethodId);
        }
        if (res == null) {
            res = cPath.getClass(functionalInterface.getClassName()).getMethodRecursively(resolvedMethodId);
        }
        return res;
    }

    @Override
    public ImmutableMap<String, Field> getStaticFields() {
        return ImmutableCreator.create(emptyMap());
    }

    @Override
    public ImmutableMap<String, Field> getInstanceFields() {
        return ImmutableCreator.create(instanceFields);
    }

    @Override
    public Field getField(String nameAndDescriptor) {
        return instanceFields.get(nameAndDescriptor);
    }

    @Override
    public boolean isFinal() {
        return true;
    }

    @Override
    public boolean isEffectivelyFinal() {
        return true;
    }

    @Override
    public Pair<Integer, Integer> getClassFileVersion() {
        return ParsedClassFile.CURRENT_VERSION;
    }

}
