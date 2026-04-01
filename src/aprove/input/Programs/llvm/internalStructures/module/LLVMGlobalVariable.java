package aprove.input.Programs.llvm.internalStructures.module;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import immutables.*;

/**
 * @author Janine Repke, CryingShadow
 *
 */
public class LLVMGlobalVariable implements Immutable {

    /**
     * The address space (TODO: non-null - default address space is zero).
     */
    private final LLVMLiteral addrSpace;

    /**
     * The alignment (optional - maybe null).
     */
    private final LLVMLiteral alignment;

    /**
     * A variable is either constant or global. Constant means that the content of the variable will never be modified.
     */
    private final boolean constant;

    /**
     * The initial value (optional - maybe null).
     */
    private final LLVMLiteral initValue;

    // TODO document me
    private final LLVMLinkageType linkageType;

    /**
     * The name of the global variable.
     */
    private final String name;

    /**
     * The section (optional - maybe null).
     */
    private final String section;

    /**
     * If true, the variable will not be shared by threads, but copied instead for every thread.
     */
    private final boolean threadLocal;

    /**
     * The type of the global variable.
     */
    private final LLVMType type;

    /**
     * @param nameParam The name of the global variable.
     * @param typeParam The type of the global variable.
     * @param addrSpaceParam The address space.
     * @param alignmentParam The alignment.
     * @param threadLocalParam If true, the variable will not be shared by threads, but copied instead for every thread.
     * @param constantParam A variable is either constant or global. Constant (true) means that the content of the
     *                      variable will never be modified.
     * @param initValueParam The initial value.
     * @param linkageTypeParam TODO
     * @param sectionParam The section.
     */
    public LLVMGlobalVariable(
        String nameParam,
        LLVMType typeParam,
        LLVMLiteral addrSpaceParam,
        LLVMLiteral alignmentParam,
        boolean threadLocalParam,
        boolean constantParam,
        LLVMLiteral initValueParam,
        LLVMLinkageType linkageTypeParam,
        String sectionParam
    ) {
        this.name = nameParam;
        this.type = typeParam;
        this.addrSpace = addrSpaceParam;
        this.alignment = alignmentParam;
        this.threadLocal = threadLocalParam;
        this.constant = constantParam;
        this.initValue = initValueParam;
        this.linkageType = linkageTypeParam;
        this.section = sectionParam;
    }

    /**
     * @return The address space.
     */
    public LLVMLiteral getAddrSpace() {
        return this.addrSpace;
    }

    /**
     * @return The alignment.
     */
    public LLVMLiteral getAlignment() {
        return this.alignment;
    }

    /**
     * @return The initial value.
     */
    public LLVMLiteral getInitValue() {
        return this.initValue;
    }

    /**
     * @return TODO
     */
    public LLVMLinkageType getLinkageType() {
        return this.linkageType;
    }

    /**
     * @return The name of the global variable.
     */
    public String getName() {
        return this.name;
    }

    /**
     * @return The section.
     */
    public String getSection() {
        return this.section;
    }

    /**
     * @return The type of the global variable.
     */
    public LLVMType getType() {
        return this.type;
    }

    /**
     * @return True iff the content of the variable will never be modified.
     */
    public boolean isConstant() {
        return this.constant;
    }

    /**
     * @return True iff the variable will not be shared by threads, but copied instead for every thread.
     */
    public boolean isThreadLocal() {
        return this.threadLocal;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder strBuilder = new StringBuilder("Name: " + this.name);
        strBuilder.append(" initVal: " + this.initValue);
        strBuilder.append(" type: " + this.type);
        strBuilder.append(" addrSpace: " + this.addrSpace);
        if (this.alignment != null) {
            strBuilder.append(" alignment: " + this.alignment);
        }
        strBuilder.append(" threadLocal: " + this.threadLocal);
        strBuilder.append(" constant: " + this.constant);
        strBuilder.append(" linkageType: " + this.linkageType);
        strBuilder.append(" section: " + this.section);
        return strBuilder.toString();
    }

}
