package aprove.input.Programs.Predef;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Typing.*;

/** Represents an abstract item which represents an object of a pre-defined data structure.
 * @author Matthias Raffelsieper
 */

public abstract class AbstractPredefItem {

    protected String nodeContent;
    protected TypeContext typeContext;
    protected Program program;

    public AbstractPredefItem() {
        this(null,null,null);
    }

    protected AbstractPredefItem(String nodeContent, TypeContext typeContext, Program program) {
        this.nodeContent = nodeContent;
        this.typeContext = typeContext;
        this.program = program;
    }


    public void setNodeContent(String nodeContent) {
        this.nodeContent = nodeContent;
    }

    public String getNodeContent() {
        return this.nodeContent;
    }


    public void setTypeContext(TypeContext typeContext) {
        this.typeContext = typeContext;
    }

    public TypeContext getTypeContext() {
        return this.typeContext;
    }


    public void setProgram(Program program) {
        this.program = program;
    }

    public Program getProgram() {
        return this.program;
    }


    /** creates a Term from an object of a pre-defined data structure
     * if necessary, the constructors and defined function symbols are added to the program
     * @return the term corresponding to the object
     */
    public abstract AlgebraTerm toTerm();



}
