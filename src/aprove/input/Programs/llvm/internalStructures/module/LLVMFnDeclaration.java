package aprove.input.Programs.llvm.internalStructures.module;

import java.util.*;
import java.util.stream.Collectors;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMFnDeclaration implements Exportable, Immutable, LLVMIRExport {

    /**
     * TODO Docu guess: The alignment of the function code.
     */
    private final LLVMLiteral alignment;

    /**
     * The function attributes.
     */
    private final ImmutableSet<LLVMFunctionAttribute> attributes;

    /**
     * The calling conventions.
     */
    private final LLVMCallingConvention callConv;

    /**
     * The name of a garbage collector for the function (optional - maybe null).
     */
    private final String garColl;

    /**
     * TODO documentation
     * TODO: what is the default linkage type?
     */
    private final LLVMLinkageType linkageType;

    /**
     * The name of the function.
     */
    private final String name;

    /**
     * The function parameters.
     */
    private final ImmutableList<LLVMFnParameter> parameters;

    /**
     * The return parameter.
     * TODO what is this for?
     */
    private final LLVMFnParameter returnParam;

    /**
     * Specifies whether this function has an variable-length argument list.
     */
    private final boolean variableLength;

    /**
     * TODO docu guess: The visibility type.
     */
    private final LLVMVisibilityType visType;

    /**
     * @param align TODO Docu guess: The alignment of the function code.
     * @param attrs The function attributes.
     * @param conventions The calling conventions.
     * @param garbage The name of a garbage collector for the function (optional - maybe null).
     * @param linkage TODO documentation
     * @param functionName The name of the function.
     * @param params The function parameters.
     * @param retParam The return parameter.
     * @param varLength Specifies whether this function has an variable-length argument list.
     * @param visibility TODO docu guess: The visibility type.
     */
    public LLVMFnDeclaration(
        LLVMLiteral align,
        ImmutableSet<LLVMFunctionAttribute> attrs,
        LLVMCallingConvention conventions,
        String garbage,
        LLVMLinkageType linkage,
        String functionName,
        ImmutableList<LLVMFnParameter> params,
        LLVMFnParameter retParam,
        boolean varLength,
        LLVMVisibilityType visibility
    ) {
        this.alignment = align;
        this.attributes = attrs;
        this.callConv = conventions;
        this.garColl = garbage;
        this.linkageType = linkage;
        this.name = functionName;
        this.parameters = params;
        this.returnParam = retParam;
        this.variableLength = varLength;
        this.visType = visibility;
    }

    /**
     * Adds the program positions occurring in this function to the specified collection.
     * @param poss A collection of program positions.
     */
    public void collectAllPositions(Collection<LLVMProgramPosition> poss) {
        // do nothing since function declarations have no program positions
    }

    /**
     * Adds the program variable names occurring in this basic block to the specified collection.
     * @param vars A collection of program variable names.
     */
    public void collectAllProgramVariableNames(Collection<String> vars) {
        // do nothing since there are no program variables in function declarations
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append("BasicFunctionType");
        res.append(eu.linebreak());
        res.append("name: ");
        res.append(eu.export(this.name));
        res.append(eu.linebreak());
        res.append(" returnParam: ");
        res.append(eu.export(this.returnParam));
        res.append(eu.linebreak());
        res.append(" parameters: (");
        boolean first = true;
        for (LLVMFnParameter parameter : this.parameters) {
            if (first) {
                first = false;
            } else {
                res.append(", ");
            }
            res.append(eu.export(parameter));
        }
        res.append(')');
        res.append(eu.linebreak());
        res.append(" variableLength: ");
        res.append(this.variableLength);
        res.append(eu.linebreak());
        res.append(" visibilityType: ");
        res.append(this.visType);
        res.append(eu.linebreak());
        res.append(" callingConvention: ");
        res.append(this.callConv);
        res.append(eu.linebreak());
        if (this.alignment != null) {
            res.append(" alignment: ");
            res.append(this.alignment);
            res.append(eu.linebreak());
        }
        if (this.garColl != null) {
            res.append(" garbage Collector: ");
            res.append(this.garColl);
            res.append(eu.linebreak());
        }
        return res.toString();
    }

    /**
     * @return TODO Docu guess: The alignment of the function code.
     */
    public LLVMLiteral getAlignment() {
        return this.alignment;
    }

    /**
     * @return The function attributes.
     */
    public ImmutableSet<LLVMFunctionAttribute> getAttributes() {
        return this.attributes;
    }

    /**
     * @return The calling conventions.
     */
    public LLVMCallingConvention getCallConv() {
        return this.callConv;
    }

    /**
     * @return The name of a garbage collector for the function.
     */
    public String getGarColl() {
        return this.garColl;
    }

    /**
     * @return TODO
     */
    public LLVMLinkageType getLinkageType() {
        return this.linkageType;
    }

    /**
     * @return The name of the function.
     */
    public String getName() {
        return this.name;
    }

    /**
     * @return The function parameters.
     */
    public ImmutableList<LLVMFnParameter> getParameters() {
        return this.parameters;
    }

    /**
     * @return The return parameter.
     */
    public LLVMFnParameter getReturnType() {
        return this.returnParam;
    }

    /**
     * @return TODO docu guess: The visibility type.
     */
    public LLVMVisibilityType getVisType() {
        return this.visType;
    }

    /**
     * @return True if this function has an variable-length argument list. False otherwise.
     */
    public boolean isVariableLength() {
        return this.variableLength;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("BasicFunctionType");
        strBuilder.append("name: \"" + this.name + "\"");
        strBuilder.append(" returnParam: " + this.returnParam);
        strBuilder.append(" parameters: (");
        boolean first = true;
        for (LLVMFnParameter parameter : this.parameters) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(parameter);
        }
        strBuilder.append(")");
        strBuilder.append(" variableLength: " + this.variableLength);
        strBuilder.append(" visibilityType: " + this.visType);
        strBuilder.append(" callingConvention: " + this.callConv);
        if (this.alignment != null) {
            strBuilder.append(" alignment: " + this.alignment);
        }
        if (this.garColl != null) {
            strBuilder.append(" garbage Collector: " + this.garColl);
        }
        return strBuilder.toString();
    }

	@Override
	public String toLLVMIR() {
		List<String> str = new ArrayList<String>();
		str.add("declare");
		str.add(this.returnParam.toLLVMIR());
		String params = this.parameters.stream().map(i -> i.toLLVMIR()).collect(Collectors.joining(", "));
		str.add(this.name + "(" + params + ")");
		return String.join(" ", str);
	}

}
