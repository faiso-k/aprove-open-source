package aprove.verification.oldframework.Haskell.Syntax;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * HaskellPreType is the pre-Typeschema form of a type of a Haskellprogram and
 * it contains a context and a matrix, if it contains Variables thier HaskellSymbols
 * are need to go through TyVarTransformerVisitor, the methode toTypeSchema does that all.
 */

public class HaskellPreType extends HaskellObject.HaskellObjectSkeleton {
    EntityFrame entityFrame;
    HaskellObject matrix;
    Context context;
    HaskellObject classConstraint;

    public HaskellPreType(Context context,HaskellObject matrix,EntityFrame entityFrame){
        this.matrix = matrix;
        this.context = context;
        this.entityFrame = entityFrame;
    }

    public Context getContext() {
        return this.context;
    }

    public HaskellObject getMatrix() {
        return this.matrix;
    }

    public HaskellPreType(Context context,HaskellObject matrix){
        this(context,matrix,null);
    }

    public void setClassConstraint(HaskellObject cc){
        this.classConstraint = cc;
    }

    public EntityFrame getEntityFrame() {
        return this.entityFrame;
    }

    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new HaskellPreType(Copy.deep(this.context),Copy.deep(this.matrix),this.entityFrame));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcasePreType(this);
        this.classConstraint = this.walk(this.classConstraint,hv);
        this.context = this.walk(this.context,hv);
        hv.icasePreType(this);
        this.matrix = this.walk(this.matrix,hv);
        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardPreTypeEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        return hv.casePreType(this);
    }

    /**
     * test if the HaskellPreType is a correct Haskell-TypeSchema
     * if this is so it return this TypeSchema
     * also it replaces the type-shortcuts (keyword "type" ) by the real long type
     */
    public TypeSchema toTypeSchema(Set<HaskellBasicRule> typeRules){
        TyVarTransformerVisitor tvtv = new TyVarTransformerVisitor();
        Context nContext = this.walk(Copy.deep(this.context),tvtv);
        HaskellObject nMatrix = this.walk(Copy.deep(this.matrix),tvtv);
        Set<ClassConstraint> ccs = nContext.toClassConstraints();
        if (!ClassConstraintGraph.constraintsInWHNF(ccs)){
            HaskellError.output(this,"illegal constraints "+ccs);
        }
        TypeSchema ts;
        if (this.classConstraint == null) {
           ts = new TypeSchema(tvtv.getQuantor(),ccs,(HaskellType)nMatrix);
        } else {
           HaskellObject nClassConstraint = this.walk(Copy.deep(this.classConstraint),tvtv);
           ClassConstraint cc = ClassConstraint.create(nClassConstraint);
           ccs.add(cc);
           ts = new MemberTypeSchema(cc,tvtv.getQuantor(),ccs,(HaskellType)nMatrix);
        }
        BasicRuleApplyVisitor brav = new BasicRuleApplyVisitor(typeRules);
        do {
           ts.visit(brav);
        } while (brav.wasActive());
        return ts;
    }
}
