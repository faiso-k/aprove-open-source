package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 */

/**
 * This class represents one rule of a function declaration in Haskell
 */
public class FuncDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl {
    protected RawTerm rexp;
    protected HaskellExp exp;
    protected HaskellSym func;
    EntityFrame entityFrame;
    boolean patternMember;

    public FuncDecl(HaskellSym func,RawTerm rexp,HaskellExp exp,EntityFrame entityFrame,boolean patternMember){
        this.func = func;
        this.rexp = rexp;
        this.exp = exp;
        this.rexp.setLHS();
        this.entityFrame = entityFrame;
    this.patternMember = patternMember;
    }

    public FuncDecl(HaskellSym func,RawTerm rexp,HaskellExp exp){
        this(func,rexp,exp,null,false);
    }


    public void setPatternMember(){
        this.patternMember = true;
    }

    public boolean isPatternMember(){
        return this.patternMember;
    }

    /**
     * retuns the symbol of the function for which this funcdecl declare one rule
     */
    public HaskellSym getFunction(){
        return this.func;
    }

    /**
     * returns true iff this FuncDecl has no pattern an declare one Variable (simple pattern binding)
     */
    public boolean isSolitary(){
        if (this.rexp.getSize() == 1) {
            if (!(this.rexp.getObjects().get(0) instanceof Apply)){
                return true;
            }
        }
        return false;
    }

    public RawTerm getRawExpression(){
        return this.rexp;
    }

    public HaskellExp getResultExpression(){
        return this.exp;
    }

    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new FuncDecl(Copy.deep(this.func),Copy.deep(this.rexp),Copy.deep(this.exp),this.entityFrame,this.patternMember));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseFuncDecl(this);
        this.func = this.walk(this.func,hv);
        this.rexp = this.walk(this.rexp,hv);
        hv.icaseFuncDecl(this);
        this.exp = this.walk(this.exp,hv);
        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardFuncDeclEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        return hv.caseFuncDecl(this);
    }

   /**
    * creates the HaskellRule for this FuncDecl
    */
    public HaskellRule createRule(){
        List<HaskellPat> pats = this.rexp.toLHS();
        pats.remove(0); // remove leading functionSymbol form patterns
        HaskellRule rule = new HaskellRule(this.entityFrame,pats,this.exp);
        rule.transferToken(this);
        return rule;
    }

}
