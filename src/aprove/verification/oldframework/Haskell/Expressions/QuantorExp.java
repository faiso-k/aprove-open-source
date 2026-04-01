package aprove.verification.oldframework.Haskell.Expressions;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The QuantorExp represents the startterms with allquantified variables, it contains
 * the expression and the local variable, and thier entities in an entityframe
 *
 * XML-Bean
 */
public class QuantorExp extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellExp, EntityFrameCarrier {
    List<Var> variables;
    HaskellExp result;
    EntityFrame entityFrame;


    /**
     * do not use this constructor, its only for bean convention
     */
    public QuantorExp(){
    }

    /**
     * constructor for deepcopy
     */
    public QuantorExp(List<Var> variables,HaskellExp result,EntityFrame entityFrame) {
         this.result = result;
         this.variables = variables;
         this.entityFrame = entityFrame;
    }

    /**
     * normal constructor
     */
    public QuantorExp(List<Var> variables,HaskellExp result) {
         this(variables,result,null);
    }

    public void setVariables(List<Var> variables){
         this.variables = variables;
    }

    public List<Var> getVariables(){
         return this.variables;
    }

    public HaskellExp getResult(){
         return this.result;
    }

    public void setResult(HaskellExp result){
         this.result = result;
    }

    @Override
    public Object deepcopy(){
         return this.hoCopy(new QuantorExp(Copy.deepCol(this.variables),Copy.deep(this.getResult()),this.entityFrame));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseQuantorExp(this);
        if (hv.guardQuantorExpVars(this)){
            this.variables = this.listWalk(this.variables,hv);
        }
        hv.icaseQuantorExp(this);
        this.result = this.walk(this.result,hv);
        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardQuantorExpEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        return hv.caseQuantorExp(this);
    }

    @Override
    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    @Override
    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

}
