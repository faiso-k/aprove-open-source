package aprove.verification.oldframework.Haskell.BasicTerms;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * represents the haskell-application of one term (functiontion) on another term (argumentument)
 *
 * XML-Bean
 */
public class Apply extends HaskellPat.HaskellObjectSkeleton implements HaskellExp,HaskellPat,BasicTerm,HaskellType,HaskellBean {
    HaskellObject function;
    HaskellObject argument;

    transient int subtermID = -1;

    /**
     * Apply is a HaskellBean so it needs an empty Constructor
     * do not use it in other context
     */
    public Apply(){
    }

    /**
     * use this constructor
     */
    public Apply(HaskellObject function,HaskellObject argument) {
        this.function = function;
        this.argument = argument;
    }


    @Override
    public void setSubtermNumber(int num) {
        this.subtermID = num;
    }

    @Override
    public int getSubtermNumber() {
        return this.subtermID;
    }


    public HaskellObject getFunction(){
        return this.function;
    }

    public HaskellObject getArgument(){
        return this.argument;
    }

    public void setFunction(HaskellObject function){
        this.function = function;
    }

    public void setArgument(HaskellObject argument){
        this.argument = argument;
    }

    @Override
    public Object deepcopy(){
        Apply copy = new Apply(Copy.deep(this.getFunction()),Copy.deep(this.getArgument()));
        copy.setSubtermNumber(this.getSubtermNumber());
        return this.hoCopy(copy);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        if (hv.outerGuardApply(this)){
            hv.fcaseApply(this);
            this.function = this.walk(this.function,hv);
            this.argument = this.walk(this.argument,hv);
            return hv.caseApply(this);
        } else {
            return this;
        }
    }

    /**
     * (interface BasicTerm)
     */
    @Override
    public BasicTerm.Sort getBasicSort(){
        return BasicTerm.Sort.APPLY;
    }

    /**
     * checks if this apply is structurally equivalent to another
     * (interface BasicTerm)
     */
    @Override
    public boolean equivalentTo(BasicTerm t){
        if (t.getBasicSort() == BasicTerm.Sort.APPLY) {
            Apply app = (Apply) t;
            return ((BasicTerm)this.getFunction()).equivalentTo((BasicTerm) app.getFunction())
                && ((BasicTerm)this.getArgument()).equivalentTo((BasicTerm) app.getArgument());
        }
        return false;
    }

    @Override
    public String toString(){
        return "("+this.function.toString()+" "+this.argument.toString()+")";
    }

}
