package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Utility.*;



/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * A ClassConstraint carries the class constraint of a typeterm. <br/>
 * example1: Num (m Int b) <br/>
 * example2: Eq a --  Eq is a typeclass, a is typevariable  <br/>
 * <br/>
 */
public class ClassConstraint extends HaskellObject.Visitable {
    HaskellSym tyClass;
    HaskellType type;

    /**
     * ClassConstraint is a HaskellBean so it needs an empty Constructor
     * do not use it in other context
     */
    public ClassConstraint(){
    }

    /**
     * named Constructor for convinience in HaskellFactory
     */
    public static ClassConstraint create(HaskellObject ho){
        Apply app = (Apply) ho;
        Cons cons = (Cons) app.getFunction();
        return new ClassConstraint(cons.getSymbol(),(HaskellType) app.getArgument());
    }

    /**
     * @param tyClass  a valid type class symbol
     * @param type the type term of this new constraint
     */
    public ClassConstraint(HaskellSym tyClass, HaskellType type){
        this.tyClass = tyClass;
        this.type = type;
    }

    /**
     * @return true if the tyClass of this constraint is defined in the prelude
     */
    public boolean isInPrelude(){
        return this.tyClass.getEntity().getModule().isPrelude();
    }

    /**
     * @param ccg current valid constraint graph
     * @return returns true if the tyClass og this constraint is a sub class of Num
     */
    public boolean isNumSubClass(ClassConstraintGraph ccg){
        return ccg.isNumSubClass(this);
    }

    /**
     * @param ccg current valid constraint graph
     * @return returns the HaskellSym of the bounded variable by this num constraint,
     *         null, if this is no num constraint or the type term is not a variable
     */
    public HaskellSym getNumClassVarSym(ClassConstraintGraph ccg){
        if (ccg.isNumSubClass(this)) {
       if (this.type instanceof Var) {
           return ((Var) this.type).getSymbol();
       }
    }
    return null;
    }

    public HaskellType getType(){
        return this.type;
    }

    public void setType(HaskellType type){
        this.type = type;
    }

    public HaskellSym getTyClass(){
        return this.tyClass;
    }

    public void setTyClass(HaskellSym tyClass){
        this.tyClass = tyClass;
    }

    @Override
    public Object deepcopy(){
        return new ClassConstraint(Copy.deep(this.tyClass),Copy.deep(this.type));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseClassConstraint(this);
        this.tyClass = this.walk(this.tyClass,hv);
        this.type = this.walk(this.type,hv);
        return hv.caseClassConstraint(this);
    }

    /**
     * structurall equivalence
     */
    public boolean equivalentTo(ClassConstraint cc){
        return (this.tyClass.equivalentTo(cc.tyClass)) && (this.type.equivalentTo(cc.type));
    }

    /**
     * if this ClassConstraint matches to the given one
     * this methode returns the substitution otherwise it returns null
     */
    public HaskellSubstitution matches(ClassConstraint cc){
        HaskellSubstitution subs = null;
        if (cc.tyClass.equivalentTo(this.tyClass)){
           subs = BasicTerm.Tools.match(Copy.deep(this.type),cc.type);
        }
        return subs;
    }

    /**
     * if this ClassConstraint unifies with the given one,
     * this method returns the mgu of both, otherwise <code>null</code> is returned
     * @param cc Other ClassConstraint to unify with
     * @return the mgu of both class constraints, or <code>null</code> if no mgu exists
     */
    public HaskellSubstitution unifies(ClassConstraint cc) {
        HaskellSubstitution subs = null;
        if (cc.tyClass.equivalentTo(this.tyClass)) {
            subs = BasicTerm.Tools.mgu(Copy.deep(this.type), cc.type);
        }
        return subs;
    }

    /**
     * substitution application for convenience
     */
    public ClassConstraint apply(HaskellSubstitution subs){
        ClassConstraint cc = Copy.deep(this);
        if (subs != null) {
            cc.type = (HaskellType) subs.applyToDestructive(cc.type);
        }
        return cc;
    }

    /**
     * convenience pure:
     * if this method is called
     * it expects the type of this is a variable, the class is defined in prelude,
     * and the parameter type is a basic number type of Haskell (Double,Int,..)
     * then it is checked if the rules will reduce the new class constraint of
     * this.tyClass and the basic number type
     *
     * this is only needed for default rules
     */
    public boolean solvedBy(HaskellType type,Set<ClassConstraintRule> rules){
        if (!(this.type instanceof Var)) {
            return false;
        }
        ClassConstraint cc = new ClassConstraint(this.tyClass,type);
        for (ClassConstraintRule rule : rules) {
           if (rule.solves(cc)) {
            return true;
        }
        }
        return false;
    }

    /**
     * convenience class for substitution application on sets of classconstriaints
     * not destructive
     */
    public static Set<ClassConstraint> massApply(HaskellSubstitution subs,Set<ClassConstraint> ccs){
        Set<ClassConstraint> res = new HashSet<ClassConstraint>();
    for (ClassConstraint cc : ccs){
       res.add(cc.apply(subs));
    }
        return res;
    }

    @Override
    public String toString(){
        return this.tyClass+" "+this.type;
    }

}
