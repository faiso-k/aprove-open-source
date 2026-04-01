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
 * This Class represents the class declaration of Haskell of the form
 * <code> class (A1 a,...,An a) => C a where {}</code>  i
 *
 */
public class ClassDecl extends TTDecl implements HaskellBean{
    Var tyVar; // class type variable
    Cons tyClass; // type class as constructor

    /**
     * do not use this constructor, its only for bean convention
     */
    public ClassDecl(){
    }

    /**
     * normal constructor
     */
    public ClassDecl(Context context,HaskellObject defType,List<HaskellDecl> decls){
        this(context,defType,decls,null);
    }

    /**
     * constructor for deepcopy
     */
    public ClassDecl(Context context,HaskellObject defType,List<HaskellDecl> decls,EntityFrame entityFrame){
        super(context,defType,decls,entityFrame);
        if (!(this.defType instanceof Apply)) {
            HaskellError.output(this.defType,"Classname expected");
        }
        Apply app = (Apply) this.defType;
        HaskellObject fu = app.getFunction();
//        HaskellObject va = HaskellTools.getLeftMost(app.getArgument());
        List<HaskellObject> exps = HaskellTools.applyFlatten(app.getArgument());
        if (exps.size() != 1) {
            HaskellError.output(app, "only one variable allowed");
        }
        HaskellObject va = exps.get(0);
        if (!(fu instanceof Cons)) {
            HaskellError.output(fu,"Classname expected");
        }
        if (!(va instanceof Var)) {
            HaskellError.output(va,"Type variable expected");
        }
        this.tyClass = (Cons) fu;
        this.tyVar = (Var) va;
        this.tyClass.setTYCLASS();
        this.tyVar.setTYPE();
    }

    public Var getTyVar(){
        return this.tyVar;
    }

    public void setTyVar(Var tyVar){
        this.tyVar = tyVar;
    }

    public Cons getTyClass(){
        return this.tyClass;
    }

    public void setTyClass(Cons tyClass){
        this.tyClass = tyClass;
    }
    /**
     * all class members have an implicit constraint to this class
     * and here the class constraint is made concrete
     */
    public HaskellObject getNewConstraint(HaskellObject ho){
        HaskellNamedSym sym = new HaskellNamedSym((HaskellNamedSym)this.tyVar.getSymbol());
        sym.transferToken(ho);
        Var var = new Var(sym);
        var.transferToken(ho);
        var.setTYPE();
        return (new Apply(this.tyClass,var)).transferToken(ho);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new ClassDecl(Copy.deep(this.context),Copy.deep(this.defType),Copy.deepCol(this.decls),this.entityFrame));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseClassDecl(this);
        this.context = this.walk(this.context,hv);
        hv.icaseClassDecl(this);
        this.defType = this.walk(this.defType,hv);
        hv.iicaseClassDecl(this);
        if (hv.guardDecls(this)){
            this.decls = this.listWalk(this.decls,hv);
        }
        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardClassDeclEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        return hv.caseClassDecl(this);
    }
}
