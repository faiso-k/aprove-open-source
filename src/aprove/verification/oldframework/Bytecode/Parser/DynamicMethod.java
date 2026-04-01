package aprove.verification.oldframework.Bytecode.Parser;

import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.Collections.*;

import java.util.*;

import org.json.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.OpCodes.*;
import aprove.verification.oldframework.Bytecode.OpCodes.FieldAccess.*;
import aprove.verification.oldframework.Bytecode.OpCodes.InvokeMethod.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class DynamicMethod implements IMethod {

    private IMethod delegate;
    private DynamicClass containingClass;
    private MethodIdentifier mid;
    private List<OpCode> code = new ArrayList<>();
    private MethodUsedVariables usedVariables;

    public DynamicMethod(IMethod delegate, DynamicClass containingClass, IClass functionalInterface, InvocationType invocationType) {
        this.delegate = delegate;
        this.containingClass = containingClass;
        for (IMethod m: functionalInterface.getMethods()) {
            if (m.isAbstract()) {
                // According to the JavaDoc of FunctionalInterface, abstract methods which overwrite methods from jlO
                // do not count as abstract methods. Thus, we skip those here.
                MethodIdentifier jloM = new MethodIdentifier(Important.JAVA_LANG_OBJECT.getClassName(), m.getName(), m.getDescriptor());
                if (containingClass.getClassPath().getClass(Important.JAVA_LANG_OBJECT).getLocalMethod(jloM) != null) {
                    continue;
                }
                assert this.mid == null : "The 'functional' inerface " + functionalInterface.getClassName() + " has several abstract methods!";
                this.mid = m.getMethodIdentifier();
            }
        }
        generateCode(delegate, containingClass, invocationType);
        this.usedVariables = new MethodUsedVariables(this);
    }

    private void generateCode(IMethod delegate, DynamicClass containingClass, InvocationType invocationType) {
        InvocationType it = invocationType;
        if (invocationType == InvocationType.NEWSPECIAL) {
            code.add(new New(delegate.getClassName()));
            code.add(new Duplicate(1, 1));
            it = InvocationType.SPECIAL;
        }
        // push captured arguments to the operand stack
        for (int i = 0; i < containingClass.getInstanceFields().size(); i++) {
            // push "this" to the operand stack
            code.add(new Load(OperandType.ADDRESS, 0));
            // the i-th captured argument is stored in the field arg$i
            FieldIdentifier fid = new FieldIdentifier(containingClass.getClassName(), InvokeDynamic.getArgName(i));
            // load the i-th captured argument
            code.add(new FieldAccess(fid, FieldAccessType.INSTANCE, FieldAccessRW.READ));
        }
        // push all parameters to the operand stack
        // together with the captured arguments, they constitute the parameter list of the actual implementation
        ParsedMethodDescriptor descriptor = mid.getDescriptor();
        for (int i = 0; i < descriptor.getArgumentCount(); i++) {
            // + 1 because we do not want to push "this"
            code.add(new Load(descriptor.getType(i).getPrimitiveType(), i + 1));
        }
        // invoke the actual implementation
        code.add(new InvokeMethod(it, delegate.getMethodIdentifier()));
        if (descriptor.getReturnType() == null) {
            code.add(new Return(OperandType.VOID));
        } else {
            code.add(new Return(descriptor.getReturnType().getPrimitiveType()));
        }
        OpCode lastOc = null;
        for (OpCode oc: code) {
            oc.setMethod(this);
            if (lastOc != null) {
                lastOc.setNextOp(oc);
                oc.setLastOp(lastOc);
            }
            lastOc = oc;
        }
    }

    @Override
    public Set<Pair<Integer, MethodIdentifier>> getLocalMethodCalls() {
        return singleton(new Pair<>(code.size() - 2, delegate.getMethodIdentifier()));
    }

    @Override
    public Collection<MethodIdentifier> getMethodCallsRecursively() {
        return union(singleton(delegate.getMethodIdentifier()), delegate.getMethodCallsRecursively());
    }

    @Override
    public boolean isRecursive() {
        return false;
    }

    @Override
    public int getNumberOfMethodCalls(MethodIdentifier methodId) {
        return 1;
    }

    @Override
    public int getNumberOfMethodCalls() {
        return 1;
    }

    @Override
    public int getNumberOfLoops() {
        return 0;
    }

    @Override
    public int getNumberOfCallsInLoops() {
        return 0;
    }

    @Override
    public int getNumberOfBranches() {
        return 0;
    }

    @Override
    public boolean writesObjects() {
        return false;
    }

    @Override
    public boolean readsObjects() {
        return true;
    }

    @Override
    public boolean hasIntLoop() {
        return false;
    }

    @Override
    public boolean usesRandom() {
        return false;
    }

    @Override
    public boolean isInLoop(int pos) {
        return false;
    }

    @Override
    public ParsedMethodDescriptor getDescriptor() {
        return mid.getDescriptor();
    }

    @Override
    public String getName() {
        return mid.getMethodName();
    }

    @Override
    public int getVarArrayLength() {
        return mid.getDescriptor().getArgumentCount() + 1;
    }

    @Override
    public int getOpStackHeight() {
        return containingClass.getInstanceFields().size() + mid.getDescriptor().getArgumentCount();
    }

    @Override
    public ClassName getClassName() {
        return containingClass.getClassName();
    }

    @Override
    public MethodIdentifier getMethodIdentifier() {
        return mid;
    }

    @Override
    public IClass getIClass() {
        return containingClass;
    }

    @Override
    public OpCode getOpcodeAt(int index) {
        return code.get(index);
    }

    @Override
    public OpCode getStart() {
        return code.get(0);
    }

    @Override
    public String getLocalVariableName(int localVarIndex, int position) {
        return "var$" + localVarIndex;
    }

    @Override
    public boolean variableUsedAt(int varIndex, int pos) {
        return usedVariables.usedAt(pos).contains(varIndex);
    }

    @Override
    public boolean isStatic() {
        return false;
    }

    @Override
    public boolean isStrictFP() {
        return false;
    }

    @Override
    public boolean isSynchronized() {
        return false;
    }

    @Override
    public boolean isNative() {
        return false;
    }

    @Override
    public boolean isAbstract() {
        return false;
    }

    @Override
    public boolean isFinal() {
        return false;
    }

    @Override
    public boolean isProtected() {
        return false;
    }

    @Override
    public boolean isPrivate() {
        return false;
    }

    @Override
    public boolean isPublic() {
        return true;
    }

    @Override
    public boolean isDefaultAccess() {
        return false;
    }

    @Override
    public boolean isInstanceInitializer() {
        return false;
    }

    @Override
    public boolean isClassInitializer() {
        return false;
    }

    @Override
    public boolean isMain() {
        return false;
    }

    @Override
    public boolean isSignaturePolymorphic() {
        return false;
    }

    @Override
    public boolean isVarArgs() {
        return false;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        throw new NotYetImplementedException();
    }

    @Override
    public void dumpMethodInfo(String fileName) {
        throw new NotYetImplementedException();
    }

    @Override
    public void setAccessible(ClassName containingClass) {
        throw new UnsupportedOperationException();
    }

}
