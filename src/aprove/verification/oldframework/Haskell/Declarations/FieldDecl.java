package aprove.verification.oldframework.Haskell.Declarations;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Matthias Raffelsieper
 * @version $Id$
 *
 * This class represents the declaration of a field
 * inside a data and newtype declaration
 */
public class FieldDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl,HaskellBean {
    EntityFrame entityFrame;
    Var field;              // the name of the field
    boolean isStrict;       // whether this field is declared to be strict
    HaskellObject type;     // the pretype or later the typeschema of the declared type constructed

    /**
     * do not use this constructor, its only for bean convention
     */
    public FieldDecl(){
    }

    /**
     * constructor for deepcopy
     */
    public FieldDecl(Var field, boolean isStrict, EntityFrame entityFrame,HaskellObject type){
        this.field = field;
        this.isStrict = isStrict;
        this.entityFrame = entityFrame;
        this.type = type;
    }

    /**
     * normal constructor
     */
    public FieldDecl(Var field, boolean isStrict, HaskellObject type){
        this(field,isStrict,null,type);
    }

    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

    public HaskellObject getType(){
       return this.type;
    }

    public void setType(HaskellObject type){
       this.type = type;
    }

    public TypeSchema getTypeSchema(){
        return (TypeSchema) this.type;
    }

    public Var getField() {
        return this.field;
    }

    public void setField(Var field) {
        this.field = field;
    }

    public void setStrict(boolean strict) {
        this.isStrict = strict;
    }

    public boolean getStrict() {
        return this.isStrict;
    }

    /**
     * returns the arity of the type constructor declared by this DataDecl
     */
    public int getArity(){
        return 1;
    }

    public HaskellSym getSymbol(){
        return this.field.getSymbol();
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new FieldDecl(Copy.deep(this.field),this.isStrict,this.entityFrame,Copy.deep(this.type)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseEntityFrame(this.entityFrame);
        hv.fcaseFieldDecl(this);

            this.type = this.walk(this.type,hv);

        hv.icaseEntityFrame(this.entityFrame);
        if (hv.guardFieldDeclEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        return hv.caseFieldDecl(this);
    }


    @Override
    public String toString() {
        return this.field + " :: "+((this.isStrict) ? "!" : "")+this.type;
    }
}
