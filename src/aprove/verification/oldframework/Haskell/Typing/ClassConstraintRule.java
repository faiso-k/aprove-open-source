package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Utility.*;



/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * ClassConstraintRule is basically the head of an instance declaration in Haskell
 * of the form:  <code>instance (C1 ai1,....,Cn ain) => B (TyCons a1 ... am) where {}</code> <br/>
 * and represents an instance reduction rule for a class constraint <br/>
 * Example of a reduction: <code>Eq (List (Maybe a))  ->  Eq (Maybe a)</code>
 * (with rule <code> Eq (List b) -> Eq b </code>)
 * <br/>
 *
 * or it is the head of a class declaration of the form:
 * <code>class (C1 a,....,Cn a) => B  a where</code>
 *
 */
public class ClassConstraintRule extends HaskellObject.Visitable implements HaskellBean {
    /**
     * <code> B (TyCons a1 ... an) </code>, the instance <br/>
     * or <code> B a </code>, the subclass
     */
    ClassConstraint pattern;

    /**
     * <code> (C1 a1,....,Cn an) </code>, the constarints for the instance <br/>
     * or <code> (C1 a,....,Cn a) </code>, the superclasses
     */
    Set<ClassConstraint> results;

    /**
     * ClassConstraintRule is a HaskellBean so it needs an empty Constructor
     * do not use it in other context
     */
    public ClassConstraintRule(){
    }

    /**
     * normal constructor
     */
    public ClassConstraintRule(ClassConstraint pattern, Set<ClassConstraint> results){
        this.pattern = pattern;
        this.results = results;
    }

    public boolean isEmpty(){
        return this.results.size()==0;
    }

    public ClassConstraint getPattern(){
        return this.pattern;
    }

    public void setPattern(ClassConstraint pattern){
        this.pattern = pattern;
    }

    public Set<ClassConstraint> getResults(){
        return this.results;
    }

    public void setResults(Set<ClassConstraint> results){
        this.results = results;
    }

    /**
     * replaces an instance constraint with the result costraints
     * @param ccs the set in which all matching constraints are replaced
     */
    public boolean applyTo(Set<ClassConstraint> ccs){
        boolean change = false;
        Set<ClassConstraint> res = new HashSet<ClassConstraint>();
        Iterator<ClassConstraint> it = ccs.iterator();
        while (it.hasNext()){
            ClassConstraint c = it.next();
            HaskellSubstitution subs = this.pattern.matches(c);
            if (subs != null) {
                it.remove();
                change = true;
                for (ClassConstraint r : this.results) {
                   res.add(r.apply(subs));
                }
            }
        }
        ccs.addAll(res);
    return change;
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.results = this.listWalk(this.results,hv);
        this.pattern = this.walk(this.pattern,hv);
        return this;
    }

    /**
     * copies this ClassConstraintRule and freshes all occuring variables
     */
    public ClassConstraintRule freshVarCopy(){
        return (ClassConstraintRule) (Copy.deep(this)).visit(new AutoRenVarSubstitutor());
    }

    @Override
    public Object deepcopy(){
       return new ClassConstraintRule(Copy.deep(this.pattern),Copy.deepCol(this.results));
    }

    /**
     * convenience for method solvedBy in class constraint
     * @return true if and only if a class constraint is solved by this rule and no new constraint remains
     */
    public boolean solves(ClassConstraint c){
        if (this.results.size() > 0) {
            return false;
        }
        return this.pattern.matches(c) != null;
    }

    /**
     * if this rule carries a class head
     * all edges resulting of this class head are added to the constraint graph
     */
    public void addEdgesTo(ClassConstraintGraph ccg){
//        ccg.addEdge(this.pattern,this.pattern);
        ccg.addNode(this.pattern.getTyClass().getEntity());
        for (ClassConstraint r : this.results){
            ccg.addEdge(this.pattern,r);
        }
    }

    /**
     * @return String representation of this rule,
     * which is as it would be written in Haskell, but from right to left
     */
    @Override
    public String toString() {
        return this.pattern.toString() + " <= " + this.results.toString();
    }
}
