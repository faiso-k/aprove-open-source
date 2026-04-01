package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 *
 * The BoundedLocalVarCollector collects all bounded Variables in a subterm
 * bounded means: Lambda bounding, Case Bounding, Let Bounding, Function Rule Bounding
 * Example: "\x -> (x,y)"   x will be collected"
 * if a bounded variable occur several times, it is only added once to the collection
 * (it will occur only once in the target collection even it is a list)
 */
public class BoundedLocalVarCollector extends HaskellVisitor{
    Collection<Var> boundedVars;
    Set<HaskellEntity> fboundedEntities;
    Set<HaskellEntity> boundedEntities;

    /**
     * @param boundedVars target collection
     */
    public BoundedLocalVarCollector(Collection<Var> boundedVars){
        this.boundedVars = boundedVars;
        this.boundedEntities = new HashSet<HaskellEntity>();
        this.fboundedEntities = new HashSet<HaskellEntity>();
    }

    @Override
    public void fcaseVar(Var ho){
        HaskellEntity entity = ho.getSymbol().getEntity();
        if (entity instanceof VarEntity) {
            if (((VarEntity)entity).getLocal()) {
                if (this.boundedEntities.contains(entity)) {
                    if(this.fboundedEntities.add(entity)) {
                        this.boundedVars.add(ho);
                    }
                }
            }
        }
    }

    @Override
    public void fcaseEntityFrame(EntityFrame ho){
        this.boundedEntities.addAll(ho.getCollectedEntities());
    }

}
