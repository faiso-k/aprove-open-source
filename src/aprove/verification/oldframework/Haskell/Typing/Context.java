package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * The Context represent the Constraint Context in a HaskellType-Signatur
 * later it is transformed to a Set of ClassConstraint. <br/>
 *
 * Example of a type-signatur:  (Eq a,Ord a) => a -> a -> Bool <br/>
 * The Context is (Eq a,Ord a)
 */
public class Context extends HaskellObject.HaskellObjectSkeleton implements HaskellBean{
    List<HaskellObject> constraints;

    public Context(List<HaskellObject> constraints){
        this.constraints = constraints;
    }

    public Context(){
        this.constraints = new Vector<HaskellObject>();
    }

    public List<HaskellObject> getConstraints(){
        return this.constraints;
    }

    public void setConstraints(List<HaskellObject> constraints){
        this.constraints = constraints;
    }

    public void addConstraint(HaskellObject cc){
        this.constraints.add(cc);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new Context(Copy.deepCol(this.constraints)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.constraints = this.listWalk(this.constraints,hv);
        return this;
    }

    public Set<ClassConstraint> toClassConstraints(){
        Set<ClassConstraint> ccs = new HashSet<ClassConstraint>();
        for(HaskellObject ho : this.constraints){
            ccs.add(ClassConstraint.create(ho));
        }
        return ccs;
    }

}
