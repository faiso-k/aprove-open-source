package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The InfixDecl represent the Infixl, Infixr or Infix statement in Haskell,
 * it contains a list of operators and the priority and fixity (priority+fixity = pixity)
 */
public class InfixDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl,AddDecl {
    public static final int FIXITY_MONO = -2; // minus get this fixity as the only prefix operator
    public static final int FIXITY_DEFAULT = -1; // all non operator symbols get this fixity
    public static final int FIXITY_NON = 0;  // infix
    public static final int FIXITY_LEFT = 1; // infixl
    public static final int FIXITY_RIGHT = 2; // infixr

    public static final int PRIORITY_DEFAULT = 9; // all non opertaor symbols get this priority

    int priority;
    int fixity;
    List<Operator> ops; // list of opertaors

    /**
     * used by the parser
     */
    public InfixDecl(int fixity, int priority, List<Operator> ops){
        this.priority = priority;
        this.fixity = fixity;
        this.ops = ops;
    }

    public int getPriority(){
        return this.priority;
    }

    public int getFixity(){
        return this.fixity;
    }

    public List<Operator> getOperators(){
        return this.ops;
    }

    /**
     *  transfers the pixity to the entities of the given EntityMap
     *  refered by the operators in the list (ops)
     */
    @Override
    public void transferTo(EntityMap entities){
        for(Operator op : this.ops){
            HaskellEntity e = entities.get(op.getAtom().getSymbol().getName(true),HaskellEntity.Sort.VAR);
            if (e == null) {
                e = entities.get(op.getAtom().getSymbol().getName(true),HaskellEntity.Sort.CONS);
            }
            if (e != null) {
                if (e.getFixity() != InfixDecl.FIXITY_DEFAULT) {
                    HaskellError.output(op,"repeated infix setting");
                }
                e.setFixity(this.fixity);
                e.setPriority(this.priority);
            } else {
                HaskellError.output(op,"undefined function");
            }
        }
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new InfixDecl(this.getFixity(),this.getPriority(),Copy.deepCol(this.ops)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseAddDecl(this);
        this.ops = this.listWalk(this.ops,hv);
        return this;
    }

}
