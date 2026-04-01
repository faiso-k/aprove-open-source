package aprove.verification.oldframework.Haskell.Expressions;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * LetExp represents the let expressionression or the where expressionression of Haskell,
 * it contains the local, declarations the expression and the mode (where or let).
 *
 * XML-Bean
 *
 */
public class LetExp extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellExp, RightTypeBinding, EntityFrameCarrier  {
    public static final int LET = 0;
    public static final int WHERE = 1;

    List<HaskellDecl> declarations; // the declarations made in this let expression
    boolean entityMode;
    EntityFrame entityFrame; // defined entities in this let expression
    List<Group> groups;  // the typechecker will save the local mutual recursive blocks as groups here
    HaskellExp expression; // the expression for which the local definitions are made
    int mode;              // let or where

    /**
     * do not use this constructor, its only for bean convention
     */
    public LetExp(){
    }

    /**
     * normal constructor
     */
    public LetExp(List<HaskellDecl> declarations, HaskellExp expression,int mode){
        this.declarations = declarations;
        this.expression = expression;
        this.mode = mode;
        this.groups = null;
        this.entityFrame = null;
        this.entityMode = false;
    }

    /**
     * constructor for deepcopy
     */
    public LetExp(List<HaskellDecl> declarations, HaskellExp expression,int mode,boolean entityMode,EntityFrame entityFrame){
        this.declarations = declarations;
        this.expression = expression;
        this.mode = mode;
        this.groups = null;
        this.entityMode = entityMode;
        this.entityFrame = entityFrame;
    }

    public void setMode(int mode){
       this.mode = mode;
    }

    public int getMode(){
       return this.mode;
    }

    public HaskellExp getExpression(){
        return this.expression;
    }

    public void setExpression(HaskellExp expression){
        this.expression = expression;
    }

    public List<Group> getGroups(){
        return this.groups;
    }

    public void setGroups(List<Group> groups){
        this.declarations.clear();
        this.groups = groups;
    }

    public List<HaskellDecl> getDeclarations(){
        return this.declarations;
    }

    public void setDeclarations(List<HaskellDecl> declarations){
        this.declarations = declarations;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new LetExp(Copy.deepCol(this.getDeclarations()),Copy.deep(this.getExpression()),this.mode,this.entityMode,this.entityFrame));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseLetExp(this);
        if (this.entityMode) {
            if (hv.guardLetFrame(this)) {
                this.entityFrame = this.walk(this.entityFrame,hv);
            }
        } else {
            this.declarations = this.listWalk(this.declarations,hv);
        }
        hv.icaseLetExp(this);
        this.expression = this.walk(this.expression,hv);
        if (hv.guardLetExpEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        if (hv.guardLetExpDecl(this)){
            this.declarations = this.listWalk(this.declarations,hv);
        }
        hv.icaseEntityFrame(this.entityFrame);
        return hv.caseLetExp(this);
    }

    /**
     * the type is shifted down to the result RawTerm
     * i.e.: <code> 4 + let x = 6 in 5 :: Int  </code><br/>
     * is transformed to <code> 4 + let x = 6 in (5 :: Int)  </code><br/>
     * cause of ugly haskell syntax.
     */
    @Override
    public void shiftTypeDown(HaskellPreType type){
        RawTerm rt = (RawTerm) this.expression;
        rt.shiftTypeDown(type);
    }

    @Override
    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    @Override
    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

    /**
     * switch to entity mode
     * in entity mode the local declarations are no longer visitable
     */
    public void setEntityMode(boolean entityMode){
        this.entityMode = entityMode;
    }

    public boolean getEntityMode(){
        return this.entityMode;
    }


}
