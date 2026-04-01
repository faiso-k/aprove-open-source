package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * Derivings represents the deriving statement of data declaration
 * it contains the list of ClassNames as list of constructors
 */

public class Derivings extends HaskellObject.HaskellObjectSkeleton implements HaskellBean {
    List<Cons> classes;


    /**
     * do not use this constructor, its only for bean convention
     */
    public Derivings(){
    }

    /**
     * the normal constructor
     */
    public Derivings(List<Cons> classes){
        this.classes = classes;
    }

    public List<Cons> getClasses(){
        return this.classes;
    }

    public void setClasses(List<Cons> classes){
        this.classes = classes;
    }

    /**
     * convenience methods to get the symbols directly
     * and not the Class-Name containing constructors
     */
    public List<HaskellSym> getClassSyms(){
        List<HaskellSym> res = new Vector<HaskellSym>();
        for (Cons c : this.classes){
            res.add(c.getSymbol());
        }
        return res;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new Derivings(Copy.deepCol(this.classes)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.classes = this.listWalk(this.classes,hv);
        return this;
    }

}
