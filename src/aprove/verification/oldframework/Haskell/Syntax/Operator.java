package aprove.verification.oldframework.Haskell.Syntax;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The Operator is created by the parser
 * and after all atoms know if they are operators or not
 * all operators are removed. (see therefore HaskellTools.Pixity)
 */
public class Operator extends HaskellObject.HaskellObjectSkeleton {

    Atom atom;

    public Operator(Atom atom){
        this.atom = atom;
    }

    public Atom getAtom(){
        return this.atom;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new Operator(Copy.deep(this.getAtom())));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.atom = this.walk(this.atom,hv);
        return hv.caseOperator(this);
    }

}
