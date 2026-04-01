package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The ConsEntity represents a Constructor of an Data-Declaration
 *
 * XML-Bean
 */

public class ConsEntity extends HaskellEntity.HaskellEntitySkeleton implements HaskellBean {
    HaskellEntity parentEntity;
    HaskellObject type;
    List<Boolean> strictness;
    boolean infix;
    boolean tupled;

    List<Var> selectors;

    /**
     * do not use this constructor, its only for bean convention
     */
    public ConsEntity(){
    }


    /**
     * normal constructor
     */
    public ConsEntity(String name,Module module,HaskellObject obj,HaskellObject type,List<Boolean> strictness,boolean infix,boolean tupled){
        this(name,module,obj,type,strictness, new LinkedList<Var>(), infix,tupled);
    }

    /**
     * normal constructor
     */
    public ConsEntity(String name,Module module,HaskellObject obj,HaskellObject type,List<Boolean> strictness,List<Var> selectors,boolean infix,boolean tupled){
        super(name,HaskellEntity.Sort.CONS,module,obj);
        this.type = type;
        this.strictness = strictness;
        this.infix = infix;
        this.tupled = tupled;
        this.selectors = selectors;
    }

    public List<Var> getSelectors() {
        return this.selectors;
    }

    @Override
    public void setParentEntity(HaskellEntity parentEntity){
        this.parentEntity = parentEntity;
    }

    @Override
    public HaskellEntity getParentEntity(){
        return this.parentEntity;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new ConsEntity(this.name,this.module,Copy.deep(this.getValue()),Copy.deep(this.getType()),new Vector<Boolean>(this.strictness),Copy.deepCol(this.selectors),this.getInfix(),this.getTupled()));
    }

    @Override
    public HaskellObject getType(){
        return this.type;
    }

    @Override
    public void setType(HaskellObject type){
        this.type = type;
    }

    /**
     * @returns Strictness-Flag-List, for each parameter of the constructor
     */
    public List<Boolean> getStrictness(){
        return this.strictness;
    }

    public void getStrictness(List<Boolean> strictness){
        this.strictness = strictness;
    }

    /**
     * the arity of the constructor represented by this ConsEntity
     */
    public int getArity(){
        return this.strictness.size();
    }

    /**
     * @returns true, if the constructor is an infix constructor
     */
    public boolean isInfix(){
        return this.infix;
    }

    public boolean getInfix(){
        return this.infix;
    }

    public void setInfix(boolean infix){
        this.infix = infix;
    }

    /**
     * for Tuple constructor the width of the tuple
     */
    @Override
    public int getTuple(){
        if (this.tupled) {
            return this.getArity();
        }
        return -1;
    }

    /**
     * @returns true, iff the constructor is a tuple constructor
     */
    public boolean getTupled(){
        return this.tupled;
    }

    public void setTupled(boolean tupled){
        this.tupled = tupled;
    }

    /**
     * @returns the types of the parameters of the constructor, with classconstraints
     */
    public Pair<Set<ClassConstraint>,List<HaskellType>> getTypeTermsPer(HaskellType typeTerm){
        TypeSchema ts = (TypeSchema) this.getType();
        List<HaskellType> typeTerms = this.module.getModules().getPrelude().deArrow(Copy.deep(ts.getMatrix()));
        HaskellType res = typeTerms.remove(typeTerms.size()-1);
        HaskellSubstitution subs = BasicTerm.Tools.mgu(res,typeTerm);
        List<HaskellType> hts = new Vector<HaskellType>();
        for (HaskellType tt : typeTerms){
            hts.add((HaskellType)subs.applyToDestructive(tt));
        }
        Set<ClassConstraint> ccs = new HashSet<ClassConstraint>();
        for (ClassConstraint cc : ts.getConstraints()){
             ccs.add(cc.apply(subs));
        }
        return new Pair<Set<ClassConstraint>,List<HaskellType>>(ccs,hts);
    }

    /*public List<HaskellType> getTypeTermsPer(HaskellType typeTerm,boolean old){
        TypeSchema ts = (TypeSchema) this.getType();
        List<HaskellType> typeTerms = this.module.getModules().getPrelude().deArrow(Copy.deep(ts.getMatrix()));
        HaskellType res = typeTerms.remove(typeTerms.size()-1);
        Substitution subs = BasicTerm.Tools.mgu(res,typeTerm);
        List<HaskellType> hts = new Vector<HaskellType>();
        for (HaskellType tt : typeTerms){
            hts.add((HaskellType)subs.applyToDestructive(tt));
        }
        Set<ClassConstraint> ccs = new HashSet<ClassConstraint>();
        for (ClassConstraint cc : ts.getConstraints()){
             ccs.add(cc.apply(subs));
        }
        return hts;
    } */

}
