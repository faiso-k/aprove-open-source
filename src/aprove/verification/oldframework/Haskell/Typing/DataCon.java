package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The DataCon represents the constructor given in a DataDecl
 * it stores the strictness and the types of the parameters
 * and also if this DataCon is notated as infix.
 * After parsing it becomes the value of a ConsEntity
 */

public class DataCon extends SymObject implements HaskellBean {
    List<HaskellObject> types;
    HaskellPreType type;
    List<Boolean> strictness;
    boolean infix;

    List<Var> fields;

    /**
     * do not use this constructor, its only for bean convention
     */
    public DataCon(){
    }

    public DataCon(HaskellSym sym,List<HaskellObject> types,boolean infix) {
         this(sym,types,null,infix);
    }

    public DataCon(HaskellSym sym, List<HaskellObject> types, boolean infix, List<Var> fields) {
        this(sym, types, null, infix);
        this.setFields(fields);
    }

    /**
     * constructor for deepcopy
     */
    public DataCon(HaskellSym sym,List<HaskellObject> types,List<Var> fields,HaskellPreType type,List<Boolean> strictness,boolean infix) {
         super(sym);
         this.types = types;
         this.fields = fields;
         this.type = type;
         this.strictness = strictness;
         this.infix = infix;
    }

    public DataCon(HaskellSym sym,List<HaskellObject> types,HaskellPreType type,boolean infix) {
         super(sym);
         this.infix = infix;
         this.strictness = new Vector<Boolean>();
         this.types = new Vector<HaskellObject>();
         this.type = type;
         for (HaskellObject ho : types){
             if (ho instanceof StrictnessFlag){
                 this.types.add(((StrictnessFlag) ho).getType());
                 this.strictness.add(true);
             } else {
                 this.types.add(ho);
                 this.strictness.add(false);
             }
         }
    }

    public void buildPreType(HaskellFactory fac,Context context,HaskellObject defType){
         HaskellObject cur = defType;
         ListIterator<HaskellObject> it = this.types.listIterator(this.types.size());
         while (it.hasPrevious()) {
             cur = fac.buildArrow(it.previous(),cur);
         }
         this.type = new HaskellConsPreType(context,cur,this.types);
    }

    public List<HaskellObject> getTypes(){
         return this.types;
    }

    public void setTypes(List<HaskellObject> types){
         this.types = types;
    }

    public List<Var> getFields() {
        return this.fields;
    }

    public void setFields(List<Var> fields) {
        this.fields = fields;
    }

    public HaskellPreType getType(){
         return this.type;
    }

    public void setType(HaskellPreType type){
         this.type = type;
    }

    public int getArity(){
         return this.types.size();
    }

    public void setStrictness(List<Boolean> strictness){
         this.strictness = strictness;
    }

    public List<Boolean> getStrictness(){
         return this.strictness;
    }

    public boolean isInfix(){
         return this.infix;
    }

    public boolean getInfix(){
         return this.infix;
    }

    public void setInfix(boolean infix){
         this.infix = infix;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new DataCon(Copy.deep(this.getSymbol()),Copy.deepCol(this.types),Copy.deepCol(this.fields),Copy.deep(this.type),new Vector(this.strictness),this.infix));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseDataCon(this);
        this.setSymbol(this.walk(this.getSymbol(),hv));
        this.type = this.walk(this.type,hv);
        if (hv.guardDataConTypes(this)){
            this.types = this.listWalk(this.types,hv);
        }
        this.fields = this.listWalk(this.fields, hv);
        return hv.caseDataCon(this);
    }


    @Override
    public String toString() {
        String res = this.getSymbol().toString();
        if (this.getFields() != null) {
            res += " { ";
            Iterator<Var> field_it = this.getFields().iterator();
            Iterator<HaskellObject> types_it = this.getTypes().iterator();
            Iterator<Boolean> strict_it = this.strictness.iterator();
            String sep = "";
            while (field_it.hasNext()) {
                String strict = (strict_it.next()) ? "!" : "";
                res += sep + field_it.next().toString()+" :: "+strict+types_it.next();
                sep = ", ";
            }
            res += " }";
        }
        return res;
    }
}
