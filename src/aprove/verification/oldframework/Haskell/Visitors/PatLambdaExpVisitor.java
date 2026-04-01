package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;

/**
 * PatLambdaExpVisitor reduce the patterns of a PatLambdaExp to the needed ones
 * example \(x:z,y+1,u) -> x
 * is reduced to \(x:_,_,_) -> x
 * so it is lazy as much it can be
 * cause the PatLambdaExp is create not so lazy
 * example:
 *        (x:xs,Just y,z) = exp
 * is transformed to
 *   uuuu = exp
 *   x  = (\(x:xs,Just y,z) -> x) uuuu
 *   xs = (\(x:xs,Just y,z) -> xs) uuuu
 *   y  = (\(x:xs,Just y,z) -> y) uuuu
 *   z  = (\(x:xs,Just y,z) -> z) uuuu
 *
 * and now this visitor transformed it to the laziest form
 *
 *   uuuu = exp
 *   x  = (\(x:_,_,_) -> x) uuuu
 *   xs = (\(_:xs,_,_) -> xs) uuuu
 *   y  = (\(_,Just y,_) -> y) uuuu
 *   z  = (\(_,_,z) -> z) uuuu
 */
public class PatLambdaExpVisitor extends HaskellVisitor{
    HashSet<HaskellEntity> visited;

    public PatLambdaExpVisitor(){
        this.visited = new HashSet<HaskellEntity>();
    }

    @Override
    public HaskellObject casePatLambdaExp(PatLambdaExp ho){
        List<HaskellPat> pats = ho.getPatterns();
        Var var = (Var)ho.getResult();

        EntityMap em = new EntityMap();
        em.add(var.getSymbol().getEntity());
        EntityFrame ef = ho.getEntityFrame();
        ef.setCollectedEntities(em);

        List<HaskellPat> npats =  new Vector<HaskellPat>();
        npats.add((HaskellPat)this.jokernize(var,pats.get(0)));
        return new LambdaExp(npats,var,ef);
    }

    @Override
    public boolean guardEntity(HaskellEntity ho){
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //boolean ww = !(ignoreSet.contains(ho));
            //System.out.println("Cur Entity: "+ho);
            //System.out.println("Visit: "+ww);
        }

        return this.visited.add(ho);
    }


    /**
     * every pattern to joker if it does not contains the variable
     */
    public HaskellObject jokernize(Var var,HaskellObject ho){
        List<HaskellObject> hos = HaskellTools.applyFlatten(ho);
        HaskellObject head = hos.remove(0);
        if (head instanceof Cons){
            boolean found = false;
            for (int i=0;i<hos.size();i++){
               HaskellObject res = this.jokernize(var,hos.get(i));
               found = found || (!(res instanceof JokerPat));
               hos.set(i,res);
            }
            hos.add(0,head);
            return found ? HaskellTools.buildApplies(hos) : new JokerPat();
        }

        if (head instanceof Var){
            return ((Var)head).getSymbol().getEntity() == var.getSymbol().getEntity() ? head : new JokerPat();
        }
        if (head instanceof IrrPat){
            IrrPat ip = (IrrPat) head;
            HaskellObject res = (HaskellPat) this.jokernize(var,ip.getPattern());
            return (res instanceof JokerPat) ? res : new IrrPat((HaskellPat)res);
        }
        if (head instanceof PlusPat){
            PlusPat pp = (PlusPat) head;
            HaskellObject res = this.jokernize(var,pp.getVariable());
            return (res instanceof JokerPat) ? res : ho;
        }
        if (head instanceof BindPat){
            BindPat bp = (BindPat) head;
            HaskellObject res = this.jokernize(var,bp.getVariable());
            return (res instanceof JokerPat) ? this.jokernize(var,bp.getSubPattern()) : res;
        }
        if (head instanceof HaskellLit){
            return new JokerPat();
        }
        return ho;
    }
}
