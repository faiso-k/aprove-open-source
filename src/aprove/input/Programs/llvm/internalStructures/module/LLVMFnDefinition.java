package aprove.input.Programs.llvm.internalStructures.module;

import java.util.Collection;
import java.util.stream.Collectors;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMFnDefinition extends LLVMFnDeclaration {


    /**
     * The basic blocks defining this function.
     */
    private final ImmutableMap<String, LLVMBasicBlock> blocks;

    /**
     * The index of the line with debug information.
     */
    private final int debugLine;

    /**
     * The name of the first block.
     */
    private final String nameOfFirstBlock;

    /**
     * TODO documentation
     */
    private final String section;

    /**
     * @param align TODO Docu guess: The alignment of the function code.
     * @param attrs The function attributes.
     * @param conventions The calling conventions.
     * @param debugLine The index of the line with debug information.
     * @param garbage The name of a garbage collector for the function (optional - maybe null).
     * @param linkage TODO documentation
     * @param functionName The name of the function.
     * @param params The function parameters.
     * @param retParam The return parameter.
     * @param varLength Specifies whether this function has an variable-length argument list.
     * @param visibility TODO docu guess: The visibility type.
     * @param sectionLit TODO documentation
     * @param firstBlock The name of the first block.
     * @param basicBlocks The basic blocks defining this function.
     */
    // CHECKSTYLE.OFF: ParameterNumber
    // A function definition does have more than 7 components.
    public LLVMFnDefinition(
    // CHECKSTYLE.ON: ParameterNumber
        LLVMLiteral align,
        ImmutableSet<LLVMFunctionAttribute> attrs,
        LLVMCallingConvention conventions,
        int debugLine,
        String garbage,
        LLVMLinkageType linkage,
        String functionName,
        ImmutableList<LLVMFnParameter> params,
        LLVMFnParameter retParam,
        boolean varLength,
        LLVMVisibilityType visibility,
        String sectionLit,
        String firstBlock,
        ImmutableMap<String, LLVMBasicBlock> basicBlocks)
    {
        super(align, attrs, conventions, garbage, linkage, functionName, params, retParam, varLength, visibility);
        this.section = sectionLit;
        this.nameOfFirstBlock = firstBlock;
        this.blocks = basicBlocks;
        this.debugLine = debugLine;
    }

    /**
     * Creates a copy of the specified function definition with the specified basic blocks instead of the original ones.
     * @param source A function defeinition.
     * @param basicBlocks The new basic blocks for the function definition.
     */
    public LLVMFnDefinition(LLVMFnDefinition source, ImmutableMap<String, LLVMBasicBlock> basicBlocks) {
        this(source.getAlignment(), source.getAttributes(), source.getCallConv(), source.getDebugLine(), source.getGarColl(),
            source.getLinkageType(), source.getName(), source.getParameters(), source.getReturnType(), source.isVariableLength(),
            source.getVisType(), source.section, source.nameOfFirstBlock, basicBlocks);
    }

    @Override
    public void collectAllPositions(Collection<LLVMProgramPosition> poss) {
        for (LLVMBasicBlock block : this.getBlocks().values()) {
            block.collectAllPositions(this.getName(), poss);
        }
    }

    @Override
    public void collectAllProgramVariableNames(Collection<String> vars) {
        for (LLVMFnParameter param : this.getParameters()) {
            vars.add(param.getName());
        }
        for (LLVMBasicBlock block : this.getBlocks().values()) {
            block.collectAllProgramVariableNames(vars);
        }
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(super.export(eu));
        res.append(eu.linebreak());
        res.append(eu.export("Basic blocks:"));
        res.append(eu.linebreak());
        for (LLVMBasicBlock block : this.blocks.values()) {
            res.append(eu.indent(block.export(eu)));
        }
        if (this.debugLine >= 0) {
            res.append(" debug line: ");
            res.append(this.debugLine);
            res.append(eu.linebreak());
        }
        return res.toString();
    }

    /**
     * @return The basic blocks defining this function.
     */
    public ImmutableMap<String, LLVMBasicBlock> getBlocks() {
        return this.blocks;
    }

    /**
     * @return The index of the line with debug information.
     */
    public int getDebugLine() {
        return this.debugLine;
    }

    /**
     * @return The name of the first block.
     */
    public String getNameOfFirstBlock() {
        return this.nameOfFirstBlock;
    }

    /**
     * @return TODO documentation
     */
    public String getSection() {
        return this.section;
    }

    /* (non-Javadoc)
     * @see aprove.input.Programs.llvm.basicStructures.FnDeclaration#toString()
     */
    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("BasicFunctionType");
        strBuilder.append("name: \"" + this.getName() + "\"");
        strBuilder.append(" linkageType: " + this.getLinkageType());
        strBuilder.append(" returnParam: " + this.getReturnType());
        strBuilder.append(" parameters: (");
        boolean first = true;
        for (LLVMFnParameter parameter : this.getParameters()) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(parameter);
        }
        strBuilder.append(")");
        strBuilder.append(" variableLength: " + this.isVariableLength());
        strBuilder.append(" visibilityType: " + this.getVisType());
        strBuilder.append(" callingConvention: " + this.getCallConv());
        if (this.getAlignment() != null) {
            strBuilder.append(" alignment: " + this.getAlignment());
        }
        if (this.debugLine >= 0) {
            strBuilder.append(" debug line: " + this.debugLine);
        }
        if (this.getGarColl() != null) {
            strBuilder.append(" garbage Collector: " + this.getGarColl());
        }
        if (this.section != null) {
            strBuilder.append(" section: " + this.section);
        }
        // blocks
        strBuilder.append("\n");
        for (LLVMBasicBlock block : this.blocks.values()) {
            strBuilder.append(block);
        }

        return strBuilder.toString();
    }

    @Override
    public String toLLVMIR() {
        StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("define @" + this.getName() + " (");
        strBuilder.append(this.getParameters().stream().map(i -> "%" + i.toLLVMIR()).collect(Collectors.joining(", ")));
        strBuilder.append(") {\n");
        this.blocks.values().forEach(b -> strBuilder.append(b.toLLVMIR()));
        strBuilder.append("}");
        return strBuilder.toString();
    }

}
