package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 *
 * The InstDecl represents the instance declaration of the form
 * <code> instance (A1 a1,...,An an) => C (co a1 ... an) where {}</code>  in Haskell,
 * it contains the type class, the type constructor and the instance matrix.
 */
public class InstDecl extends TTDecl implements HaskellBean {
    Cons tyClass; // this instance is for this class
    Cons tyCo; // the instance type-constructor
    HaskellObject instanceMatrix; // the instance matrix

    /**
     * do not use this constructor, its only for bean convention
     */
    public InstDecl() {
    }

    /**
     * normal constructor
     */
    public InstDecl(final Context context, final HaskellObject defType, final List<HaskellDecl> decls) {
        this(context, defType, decls, null);
    }

    /**
     * constructor for deepcopy
     */
    public InstDecl(final Context context, final HaskellObject defType, final List<HaskellDecl> decls,
            final EntityFrame entityFrame) {
        super(context, defType, decls, entityFrame);
        final Apply app = HaskellTools.getLeftMostApply(this.defType);
        if (app == null) {
            HaskellError.output(app, "Instance expected");
        }
        assert (app != null);
        final HaskellObject fu = app.getFunction();
        this.instanceMatrix = app.getArgument();
        //        HaskellObject co = HaskellTools.getLeftMost(this.instanceMatrix);
        final List<HaskellObject> exps = HaskellTools.applyFlatten(this.instanceMatrix);
        final HaskellObject co = exps.remove(0);
        for (final HaskellObject ho : exps) {
            if (!(ho instanceof Var)) {
                HaskellError.output(ho, "Variable expected");
            }
        }

        if (!(fu instanceof Cons)) {
            HaskellError.output(fu, "Classname expected");
        }
        if (!(co instanceof Cons)) {
            HaskellError.output(co, "Type constructor expected");
        }
        this.tyClass = (Cons) fu;
        this.tyCo = (Cons) co;
        this.tyClass.setTYCLASS();
        this.tyCo.setTYPE();
    }

    public Cons getTyClass() {
        return this.tyClass;
    }

    public void setTyClass(final Cons tyClass) {
        this.tyClass = tyClass;
    }

    public Cons getTyCo() {
        return this.tyCo;
    }

    public void setTyCo(final Cons tyCo) {
        this.tyCo = tyCo;
    }

    public HaskellObject getInstanceMatrix() {
        return this.instanceMatrix;
    }

    public void setInstanceMatrix(final HaskellObject instanceMatrix) {
        this.instanceMatrix = instanceMatrix;
    }

    /**
     * @return the instance type schema i.e.:<br/>
     *         <code>[a1,...,an] : (A1 a1,...,An an) => co a1 ... an</code>
     */
    public TypeSchema getInstTypeSchema() {
        final TyVarTransformerVisitor tvtv = new TyVarTransformerVisitor();
        Context ct = Copy.deep(this.context);
        HaskellObject im = Copy.deep(this.instanceMatrix);
        ct = (Context) ct.visit(tvtv);
        im = im.visit(tvtv);
        return new TypeSchema(tvtv.getQuantor(), ct.toClassConstraints(), (HaskellType) im);
    }

    /**
     * @return the entity of the type class
     */
    public HaskellEntity getTyClassEntity() {
        return this.tyClass.getSymbol().getEntity();
    }

    public HaskellEntity getTyConsEntity() {
        return this.tyCo.getSymbol().getEntity();
    }

    public HaskellType getInstTypeTerm() {
        return (HaskellType) ((Apply) this.defType).getArgument();
    }

    @Override
    public Object deepcopy() {
        return this.hoCopy(new InstDecl(Copy.deep(this.context), Copy.deep(this.defType), Copy.deepCol(this.decls),
            this.entityFrame));
    }

    /**
     * @return a unique name to represent this instance, i.e.: typeclass$typeconstructor
     */
    public String getName() {
        return this.tyClass.getSymbol().getName(false) + "$" + this.tyCo.getSymbol().getName(false);
    }

    @Override
    public HaskellObject visit(final HaskellVisitor hv) {
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseInstDecl(this);
        this.context = this.walk(this.context, hv);
        hv.icaseInstDecl(this);
        this.tyClass = this.walk(this.tyClass, hv);
        this.tyCo = this.walk(this.tyCo, hv);
        this.defType = this.walk(this.defType, hv);
        hv.iicaseInstDecl(this);
        if (hv.guardDecls(this)) {
            this.decls = this.listWalk(this.decls, hv);
        }
        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardInstDeclEntityFrame(this)) {
            this.entityFrame = this.walk(this.entityFrame, hv);
        }
        return hv.caseInstDecl(this);
    }
}
