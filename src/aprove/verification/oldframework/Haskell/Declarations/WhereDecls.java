package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * represents a where declaration of a rule
 * used by the parser. it is later transformed to a let object in where-Mode
 */
public class WhereDecls extends HaskellObject.HaskellObjectSkeleton {
    List<HaskellDecl> decls;

    public WhereDecls(List<HaskellDecl> decls){
        this.decls = decls;
    }

    public List <HaskellDecl> getDeclarations(){
        return this.decls;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new WhereDecls(Copy.deepCol(this.decls)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.decls = this.listWalk(this.decls,hv);
        return this;
    }


}
