package aprove.verification.oldframework.Haskell;

import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The HaskellNamedSym is a HaskellSym with a real non null hsname and a non null entity.
 * That it has a non null entity is gurantied by the SetSymbolEntityVisitor
 * which is applied before.
 */

public class HaskellNamedSym extends HaskellSym  {
    public static boolean kill = false;
    public static boolean pill = false;
    boolean mark = false;
    HaskellEntity entity;
    String qualifier;        // module qualifier not the module itself, cause A.f could refer to f in Module K
    String hsname;        // hsname
    private int tuple;  // if this is a tuple symbol like (,,), it is the width of the tuple
    boolean operator;         // true if this HaskellSym refrer to an operator

    /**
     * HaskellNamedSym is a HaskellBean so it needs an empty Constructor
     * do not use it in other context
     */
    public HaskellNamedSym(){
    }

    /**
     *
     */
    public HaskellNamedSym(HaskellNamedSym sym){
        this.tuple = -1;
        this.hsname = sym.hsname;
        this.qualifier = sym.qualifier;
        this.entity = null;
        this.operator = false;
    }

    /**
     * creates a HaskellNamedSym which refers to the HaskellEntity
     * with the unqualified name of the HaskellEntity
     * the Symbol is an operator if the HaskellEntity has a non default fixity
     */
    public HaskellNamedSym(HaskellEntity e){
        this("",e.getName(),e);
        this.operator = (e.getFixity() > InfixDecl.FIXITY_DEFAULT);
        this.tuple = e.getTuple();
    }

    /**
     * creates a HaskellNamedSym with a qualifier and an unset entity
     */
    public HaskellNamedSym(String qualifier,String hsname){
        this.tuple = -1;
        this.hsname = hsname;
        this.qualifier = qualifier;
        this.entity = null;
        this.operator = false;
    }

    /**
     * normal constructor
     */
    public HaskellNamedSym(String qualifier,String hsname,HaskellEntity entity){
        this.tuple = -1;
        this.hsname = hsname;
        this.qualifier = qualifier;
        this.operator = false;
        //this.entity = entity;
        this.setEntity(entity);
    }

    /**
     * a HaskellNamedSym can refer to the tuple constructor and
     * this methods returns the width of the tuple constructor
     * or -1 if this symbol does not refer to a tuple constructor
     */
    @Override
    public void setTuple(int i){
        this.tuple = i;
    }

    @Override
    public int getTuple(){
       return this.tuple;
    }

    /**
     * creates a qualified or unqualified HaskellNamedSym
     * by analysing the given qname
     */
    public HaskellNamedSym(String qname){
        super();
        this.tuple = -1;
        int point = qname.indexOf('.');
        if (point>0) {
           this.qualifier = qname.substring(0,point);
           this.hsname = qname.substring(point+1);
        } else {
           this.hsname = qname;
           this.qualifier = "";
        }
        this.setEntity(null);
    }

    /**
     * @param check true if this symbol has a non empty qualifier a HaskellError is thrown
     * @return the unqualified hsname of this symbol
     */
    @Override
    public String getName(boolean check){
        if (check && !("".equals(this.qualifier))) {

          // XXX DEBUG
          if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
              System.out.println("!!!No qualifier allowed"+this.qualifier +"."+this.hsname+ " -- " + this.tok.getLine()+ ":"+this.tok.getPos());
          }
            HaskellError.output(this,"No qualifier allowed");
        }
        return this.hsname;
    }

    /**
     * return true iff this symbol is the plus "+"
     */
    @Override
    public boolean isPlusSym(){
       return ("+".equals(this.hsname)) && ("".equals(this.qualifier));
    }

    /**
     * return the unqualified name
     */
    public String getNoQualName(){
        return this.hsname;
    }

    public void setName(String hsname){
        this.hsname = hsname;
    }

    public void setHsname(String hsname){
        this.hsname = hsname;
    }

    public String getHsname(){
        return this.hsname;
    }

    @Override
    public String getQualifier(){
       return this.qualifier;
    }

    public void setQualifier(String qualifier){
       this.qualifier = qualifier;
    }

    @Override
    public void setOperator(boolean operator){
       this.operator = operator;
    }

    @Override
    public boolean getOperator(){
       return this.operator;
    }

    @Override
    public void setEntity(HaskellEntity entity){
       /*if (pill) {
           if ("Char".equals(hsname)) {
             if (((HaskellObject.Visitable)entity).flag == 00) {
                 throw new RuntimeException("Willi");
             }
           }
       }*/
       this.entity = entity;
    }

    @Override
    public HaskellEntity getEntity(){
       return this.entity;
    }

    /**
     * returns true,iff the HaskellEntity has the same name as this symbol
     */
    @Override
    public boolean matchNQ(HaskellEntity e){
       return e.getName().equals(this.hsname);
    }


    /**
     * returns true,iff the given Symbol has the same name as this symbol
     */
    @Override
    public boolean matchNQ(HaskellSym e){
       return e.getName(false).equals(this.hsname);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
       hv.fcaseHaskellSym(this);
       hv.fcaseHaskellNamedSym(this);
       if (hv.guardHaskellNamedSym(this)){
           this.entity = this.walk(this.entity,hv);
       }
       return hv.caseHaskellNamedSym(this);
    }

    /**
     * @return true, if and only if thier entities refers to is the same entity.
     */
    @Override
    public boolean equivalentTo(HaskellSym sym){
       if (sym instanceof HaskellNamedSym) {
           return sym.getEntity() == this.getEntity();
       }
       return false;
    }

    /**
     *  HaskellNamedSym is equivalent to another
     *  if they refer to the same HaskellEntity (references are the same)
     */
    @Override
    public boolean equals(Object obj){
        if (obj instanceof HaskellNamedSym) {
            return ((HaskellNamedSym) obj).getEntity() == this.getEntity();
        }
        return false;
    }

    /**
     * the hashCode is the hashCode of the entity or in case the entity is null
     * it is the normal hashCode
     */
    @Override
    public int hashCode(){
        HaskellEntity e = this.getEntity();
        if (e == null) {
            return super.hashCode();
        }
        return e.hashCode();
    }

    @Override
    public Object deepcopy(){
       return this.freshCopy();
    }

    public HaskellNamedSym freshCopy(){
       HaskellNamedSym hns = new HaskellNamedSym(this);
       /*if (kill && ("->".equals(this.hsname))

       && (this.getEntity() != null)
       ){
       if (((HaskellEntity.Skeleton)this.getEntity()).num == 0) {
       HaskellSym.showee(this);
       throw new RuntimeException("dddd "+this.getClass());
       }
       }*/
       hns.setEntity(this.getEntity());
       hns.setOperator(this.getOperator());
       hns.setTuple(this.getTuple());
       return (HaskellNamedSym) this.hoCopy(hns);
    }

    @Override
    public String toString(){
       return this.hsname;
    }

    @Override
    public boolean isNamed(){
       return true;
    }

}
