package aprove.verification.oldframework.Haskell.Qualifiers;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 * the let qualifier in do-structurs or list comprehension
 * exists only in the parser. It is later expanded to a let-expression
 */
public class LetQual extends HaskellObject.HaskellObjectSkeleton implements HaskellQual {
    List<HaskellDecl> decls;

    public LetQual(List<HaskellDecl> decls){
        this.decls = decls;
    }

    public List<HaskellDecl> getDeclarations(){
        return this.decls;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new LetQual(Copy.deepCol(this.getDeclarations())));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.decls = this.listWalk(this.decls,hv);
        return this;
    }

    @Override
    public HaskellExp toMonad(DoCompFactory fac,HaskellExp next){
        return fac.buildMonadLet(this.decls,next,this);
    }

    @Override
    public HaskellExp toListComp(DoCompFactory fac,HaskellExp next){
        return fac.buildListCompLet(this.decls,next,this);
    }


}
