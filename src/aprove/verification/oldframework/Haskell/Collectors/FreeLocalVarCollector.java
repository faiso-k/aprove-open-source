package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 * FreeLocalVarCollector collects free variables (not bounded by EntityFrames)
 * which are local and are not defined in a let expression or module.
 */
public class FreeLocalVarCollector extends HaskellVisitor{
    Collection<Var> freeVars;
    Set<HaskellEntity> freeEntities;
    Set<HaskellEntity> boundedEntities;

    public FreeLocalVarCollector(Collection<Var> freeVars){
        this.freeVars = freeVars;
        this.freeEntities = new HashSet<HaskellEntity>();
        this.boundedEntities = new HashSet<HaskellEntity>();
    }

    public FreeLocalVarCollector(Collection<Var> freeVars,Set<HaskellEntity> boundedEntities){
        this.freeVars = freeVars;
        this.freeEntities = new HashSet<HaskellEntity>();
        this.boundedEntities = boundedEntities;
    }

    @Override
    public void fcaseVar(Var ho){
        if (this.freeVars != null) {
            HaskellEntity entity = ho.getSymbol().getEntity();
            if (entity instanceof VarEntity) {
                if (((VarEntity)entity).getLocal()) {
                    if (!this.boundedEntities.contains(entity)) {
                        if(this.freeEntities.add(entity)) {
                            this.freeVars.add(ho);
                        }
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
