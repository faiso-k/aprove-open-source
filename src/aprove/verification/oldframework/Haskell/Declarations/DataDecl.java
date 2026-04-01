package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This class represents the data declaration
 * and the new type declaration of Haskell
 */
public class DataDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl,HaskellBean {
    EntityFrame entityFrame;
    Context context; // context pre form of class contsraints
    HaskellObject defType; // the defined type
    List<DataCon> dataCons; // the dataconstructors
    boolean newType;        // true, iff this DataDecl represents a newType declaration
    Derivings derivings;    // the derivings if the DataDecl has some
    HaskellObject type;     // the pretype or later the typeschema of the declared type constrructed
                            // by this DataDecl

    /**
     * do not use this constructor, its only for bean convention
     */
    public DataDecl(){
    }

    /**
     * constructor for deepcopy
     */
    public DataDecl(Context context,HaskellObject defType,List<DataCon> dataCons,boolean newType,Derivings derivings,EntityFrame entityFrame,HaskellObject type){
        this.context = context;
        this.defType = defType;
        this.dataCons = dataCons;
        this.newType = newType;
        this.derivings = derivings;
        this.entityFrame = entityFrame;
        this.type = type;
    }

    /**
     * normal constructor
     */
    public DataDecl(Context context,HaskellObject defType,List<DataCon> dataCons,boolean newType,Derivings derivings){
        this(context,defType,dataCons,newType,derivings,null,new HaskellPreType(context,defType));
    }

    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

    public boolean getNewType(){
        return this.newType;
    }

    public void setNewType(boolean newType){
        this.newType = newType;
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

    public TypeSchema getTypeSchema(){
        return (TypeSchema) this.type;
    }

    public Derivings getDerivings(){
        return this.derivings;
    }

    public void setDerivings(Derivings derivings){
        this.derivings = derivings;
    }

    public Context getContext(){
        return this.context;
    }

    public void setContext(Context context){
        this.context = context;
    }

    public List<DataCon> getDataCons(){
        return this.dataCons;
    }

    public void setDataCons(List<DataCon> dataCons){
        this.dataCons = dataCons;
    }

    /**
     * returns the arity of the type constructor declared by this DataDecl
     */
    public int getArity(){
        return HaskellTools.applyFlatten(this.defType).size()-1;
    }

    public HaskellSym getSymbol(){
        List<HaskellObject> hos = HaskellTools.applyFlatten(this.defType);
        HaskellObject obj = HaskellTools.getLeftMost(this.defType);
        hos.remove(0);
        for (HaskellObject ho : hos){
            if (!(ho instanceof Var)) {
                HaskellError.output(ho,"Variable expected");
            }
        }
        if (!(obj instanceof Cons)){
            HaskellError.output(obj,"Type constructor expected");
        }
        Cons cons = (Cons) obj;
        return cons.getSymbol();
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new DataDecl(Copy.deep(this.context),Copy.deep(this.defType),Copy.deepCol(this.dataCons),this.newType,Copy.deep(this.derivings),this.entityFrame,Copy.deep(this.type)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseDataDecl(this);
        this.context = this.walk(this.context,hv);
        hv.icaseDataDecl(this);
        this.defType = this.walk(this.defType,hv);
        hv.iicaseDataDecl(this);
        if (hv.guardDataType(this)){
            this.type = this.walk(this.type,hv);
        }
        if (hv.guardConss(this)) {
            this.dataCons = this.listWalk(this.dataCons,hv);
        }
        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardDataDeclEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        if (hv.guardDerivings(this)) {
            this.derivings = this.walk(this.derivings,hv);
        }
        return hv.caseDataDecl(this);
    }

}
