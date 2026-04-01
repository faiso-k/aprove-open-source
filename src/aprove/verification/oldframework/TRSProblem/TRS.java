package aprove.verification.oldframework.TRSProblem;


import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * @author thiemann, nowonder
 *
 * created on 19.12.2003
 */
public class TRS extends DefaultBasicObligation {
    private Program prog;
    private boolean innermost;
    private boolean createIndex = true;
    private boolean showObligation = false;
    
    private final int hashCode;

    public TRS(String name, Program prog, boolean innermost) {
        super(name, name);
        this.prog = prog;
        this.innermost = innermost;
        
        this.hashCode = this.prog.getRules().hashCode();
    }

    public TRS(Program prog, boolean innermost) {
        this("TRS", prog, innermost);
    }

    public Program getProgram() {
        return this.prog;
    }
    public boolean isEquational() {
        return this.prog.isEquational();
    }
    public boolean getInnermost() {
        return this.innermost;
    }

    public boolean isConditional() {
    return this.prog.isConditional();
    }

    public TRS deepercopy() {
    TRS temp = new TRS(this.prog.deepercopy(), this.innermost);
    return temp;
    }

    @Override
    public aprove.prooftree.Obligations.BasicObligation deepcopy() {
        return this.deepercopy();
    }

    @Override
    public BasicObligation maybeCopy() {
        return this;
    }

    public aprove.prooftree.Obligations.BasicObligation shallowcopy() {
        return new TRS(this.prog, this.innermost);
    }

    public boolean isNonOverlapping() {
        return this.prog.isNonOverlapping();
    }
    
    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object obj) {

    if (!(obj instanceof TRS)) {
        return false;
    }
    TRS otherTRS = (TRS) obj;
    if (this.getProgram().getRules().equals(otherTRS.getProgram().getRules())
        && this.getInnermost() == otherTRS.getInnermost()) {
        return true;
    }

    return false;

    }

    @Override
    public String export(Export_Util o) {
        return this.prog.export(o);
    }

    public boolean isEmpty() {
    return this.prog.isEmpty();
    }

    public boolean showObligation() {
    return this.showObligation;
    }

    public void setShowObligation(boolean show) {
    this.showObligation = show;

    }

    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public boolean isCreateIndex() {
        return this.createIndex;
    }

    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setCreateIndex(boolean createIndex) {
        this.createIndex = createIndex;
    }

    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public Program getProg() {
        return this.prog;
    }

    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setProg(Program prog) {
        this.prog = prog;
    }

    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public boolean isShowObligation() {
        return this.showObligation;
    }

    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setInnermost(boolean innermost) {
        this.innermost = innermost;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this,
                this.getInnermost()?"Innermost Termination":"Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        if (this.getProgram().isMaxUnary()) {
            return "srs";
        } else if (this.getProgram().isEquational()) {
            return "etes";
        } else {
            return "trs";
        }
    }
}
