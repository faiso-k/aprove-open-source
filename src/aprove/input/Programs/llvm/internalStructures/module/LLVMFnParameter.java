package aprove.input.Programs.llvm.internalStructures.module;

import java.util.List;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.utils.*;

import java.util.ArrayList;

import immutables.*;

/**
 * Name, type, and attributes of a function parameter (including return values).
 * @author Janine Repke, CryingShadow
 */
public class LLVMFnParameter implements Immutable, LLVMIRExport {

    /**
     * The attributes of the parameter.
     */
    private final ImmutableSet<LLVMParameterAttribute> attributes;

    /**
     * The name of the parameter (optional - parameters do have a name in function definitions, but not in function
     * declarations).
     */
    private final String name;

    /**
     * The type of the parameter.
     */
    private final LLVMType type;

    /**
     * @param paramName The name of the parameter (optional - parameters do have a name in function definitions, but
     *                  not in function declarations).
     * @param paramType The type of the parameter.
     * @param paramAttrs The attributes of the parameter.
     */
    public LLVMFnParameter(String paramName, LLVMType paramType, ImmutableSet<LLVMParameterAttribute> paramAttrs) {
        this.name = paramName;
        this.type = paramType;
        this.attributes = paramAttrs;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof LLVMFnParameter) {
            LLVMFnParameter other = (LLVMFnParameter) o;
            return (this.name == null && other.name == null || this.name.equals(other.name))
                && (this.type == null && other.type == null || this.type.equals(other.type))
                && (this.attributes == null && other.attributes == null || this.attributes.equals(other.attributes));
        }
        return false;
    }

    /**
     * @return The attributes of the parameter.
     */
    public ImmutableSet<LLVMParameterAttribute> getAttributes() {
        return this.attributes;
    }

    /**
     * @return The name of the parameter.
     */
    public String getName() {
        return this.name;
    }

    /**
     * @return The type of the parameter.
     */
    public LLVMType getType() {
        return this.type;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return 13
        // name
        * ((this.name == null ? 0 : this.name.hashCode())
        // type
            + (this.type == null ? 0 : this.type.hashCode())
        // attributes
        + (this.attributes == null ? 0 : this.attributes.hashCode()));
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder str = new StringBuilder();
        boolean first = true;
        if (this.name != null) {
            first = false;
            str.append(this.name);
        }
        if (this.type != null) {
            if (first) {
                first = false;
            } else {
                str.append(" ");
            }
            str.append(this.type);
        }
        if (this.attributes != null) {
            for (LLVMParameterAttribute attr : this.attributes) {
                if (first) {
                    first = false;
                } else {
                    str.append(" ");
                }
                str.append(attr);
            }
        }
		return str.toString();
	}

	@Override
	public String toLLVMIR() {
//        StringBuilder str = new StringBuilder();
//        boolean first = true;
//        if (this.name != null) {
//            first = false;
//            str.append(this.name);
//        }
//        if (this.type != null) {
//            if (first) {
//                first = false;
//            } else {
//                str.append(" ");
//            }
//            str.append(this.type);
//        }
//        if (this.attributes != null) {
//            for (LLVMParameterAttribute attr : this.attributes) {
//                if (first) {
//                    first = false;
//                } else {
//                    str.append(" ");
//                }
//                str.append(attr);
//            }
//        }
//		return str.toString();
		List<String> str = new ArrayList<String>();
		if(this.name != null) str.add(this.name);
		if(this.type != null) str.add(this.type.toLLVMIR());
		this.attributes.forEach(a -> str.add(a.toLLVMIR()));
		return String.join(" ", str);
	}

}
