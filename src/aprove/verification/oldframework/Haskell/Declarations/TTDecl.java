package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * base class of classDecl and InstDecl
 * contains the head representation and the local declarations
 */
public abstract class TTDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl,HaskellBean {
    EntityFrame entityFrame;
    Context context;
    HaskellObject defType;
    public List<HaskellDecl> decls;

    /**
     * do not use this constructor, its only for bean convention
     */
    public TTDecl(){
    }

    /**
     * normal constructor
     */
    public TTDecl(Context context,HaskellObject defType,List<HaskellDecl> decls,EntityFrame entityFrame){
        this.context = context;
        this.defType = defType;
        this.decls = decls;
        this.entityFrame = entityFrame;
    }

    /**
     * the head of an instance or class declaration is represented by a
     * ClassConstraintRule
     * this representation is return by this methode
     */
    public ClassConstraintRule getClassConstraintRule(){
        TyVarTransformerVisitor tvtv = new TyVarTransformerVisitor();
        Context ct = Copy.deep(this.context);
        HaskellObject dt = Copy.deep(this.defType);
        ct = (Context) ct.visit(tvtv);
        dt = dt.visit(tvtv);
        return new ClassConstraintRule(ClassConstraint.create(dt),
                                       ct.toClassConstraints());
    }

    public List<HaskellDecl> getDecls(){
        return this.decls;
    }

    public void setDecls(List<HaskellDecl> decls){
        this.decls = decls;
    }

    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

    public HaskellObject getDefType(){
       return this.defType;
    }

    public void setDefType(HaskellObject defType){
       this.defType = defType;
    }

    public Context getContext(){
        return this.context;
    }

    public void setContext(Context context){
        this.context = context;
    }

    public HaskellSym getSymbol(){
        HaskellObject obj = HaskellTools.getLeftMost(this.defType);
        if (!(obj instanceof Cons)){
            HaskellError.output(obj,"Type constructor expected");
        }
        Cons cons = (Cons) obj;
        return cons.getSymbol();
    }

}
