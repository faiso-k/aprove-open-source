package aprove.verification.oldframework.Haskell.Declarations;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * SynTypeDecl represents the synonym type Declaration.
 * example: type Hallo b a = (List a,b)
 */
public class SynTypeDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl {
    EntityFrame entityFrame; // list of type variable entities
    HaskellObject defType;   // the defined type
    HaskellObject type;      // the real type

    /**
     * for bean convention
     */
    public SynTypeDecl(){
    }

    /**
     * use this constructor for deepcopy
     */
    public SynTypeDecl(HaskellObject defType,HaskellObject type,EntityFrame entityFrame){
        this.defType = defType;
        this.type = type;
        this.entityFrame = entityFrame;
    }

    /**
     * use this constructor normally
     */
    public SynTypeDecl(HaskellObject defType,HaskellObject type){
        this(defType,type,null);
    }

   public HaskellObject getType(){
       return this.type;
    }

    public void setType(HaskellObject type){
       this.type = type;
    }

    public HaskellObject getDefType(){
       return this.defType;
    }

    public void setDefType(HaskellObject defType){
       this.defType = defType;
    }

    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

    public HaskellSym getSymbol(){
        HaskellObject obj = HaskellTools.getLeftMost(this.defType);
        if (!(obj instanceof Cons)){
             HaskellError.output(obj,"Type constructor expected");
        }
        Cons cons = (Cons) obj;
        return cons.getSymbol();
    }

    /**
     * construct a basicRule for a later application on all types
     */
    public HaskellBasicRule buildTypeRule(){
       HaskellVisitor tvtv = new TyVarTransformerVisitor();
       BasicTerm l = (BasicTerm)Copy.deep(this.defType).visit(tvtv);
       BasicTerm r = (BasicTerm)Copy.deep(this.type).visit(tvtv);
       return new HaskellBasicRule.HaskellBasicRuleSkeleton(l,r);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new SynTypeDecl(Copy.deep(this.defType),Copy.deep(this.type),this.entityFrame));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseSynTypeDecl(this);
        if (hv.guardDefType(this)){
            this.defType = this.walk(this.defType,hv);
        }
        hv.icaseSynTypeDecl(this);
        this.type = this.walk(this.type,hv);
        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardSynTypeDeclEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        return hv.caseSynTypeDecl(this);
    }
}
