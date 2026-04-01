package aprove.verification.complexity.LowerBounds.Types;

import java.util.*;

import aprove.prooftree.Export.Utility.*;

public class FunctionSymbolSimpleType implements Exportable {

    public static final FunctionSymbolSimpleType Nats = new FunctionSymbolSimpleType(Type.Nats);

    public static final FunctionSymbolSimpleType Bool = new FunctionSymbolSimpleType(Type.Bool);

    private List<Type> argumentTypes;

    private Type returnType;

    public FunctionSymbolSimpleType(Type returnType,
            List<Type> argumentTypes) {
        this.returnType = returnType;
        this.argumentTypes = argumentTypes;
    }

    public FunctionSymbolSimpleType(Type returnType, Type... argTypes) {
        this(returnType, Arrays.asList(argTypes));
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        FunctionSymbolSimpleType other = (FunctionSymbolSimpleType) obj;
        if (this.argumentTypes == null) {
            if (other.argumentTypes != null) {
                return false;
            }
        } else if (!this.argumentTypes.equals(other.argumentTypes)) {
            return false;
        }
        if (this.returnType == null) {
            if (other.returnType != null) {
                return false;
            }
        } else if (!this.returnType.equals(other.returnType)) {
            return false;
        }
        return true;
    }

    public List<Type> getArgumentTypes() {
        return this.argumentTypes;
    }

    public Type getReturnType() {
        return this.returnType;
    }

    private int numberOfRecursiveArgs() {
        int n = 0;
        for (Type argType: this.argumentTypes) {
            if (argType.equals(this.returnType)) {
                n++;
            }
        }
        return n;
    }

    public boolean isRecursive() {
        return this.numberOfRecursiveArgs() > 0;
    }

    public boolean isLinear() {
        return this.numberOfRecursiveArgs() == 1;
    }

    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result =
            prime
                * result
                + ((this.argumentTypes == null) ? 0
                    : this.argumentTypes.hashCode());
        result =
            prime * result
                + ((this.returnType == null) ? 0 : this.returnType.hashCode());
        return result;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (Type a : this.argumentTypes) {
            sb.append(a + " -> ");
        }
        sb.append(this.returnType);
        return sb.toString();
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        for (Type t: this.argumentTypes) {
            sb.append(t.export(eu));
            sb.append(eu.escape(" ")).append(eu.rightarrow()).append(eu.escape(" "));
        }
        sb.append(this.returnType.export(eu));
        return sb.toString();
    }
}