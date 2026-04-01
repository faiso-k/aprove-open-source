package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class TypeDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl,AddDecl {
    protected List<Var> vars;
    protected HaskellPreType type;

    public TypeDecl(List<Var> vars,HaskellPreType type){
        this.vars = vars;
        this.type = type;
    }

    public HaskellPreType getType(){
        return this.type;
    }

    public List<Var> getVariables(){
        return this.vars;
    }

    @Override
    public void transferTo(EntityMap entities){
        for(Var var : this.vars){
            HaskellEntity e = entities.get(var.getSymbol().getName(true),HaskellEntity.Sort.VAR);
            if (e != null) {
                if (e.getType() != null) {
                    HaskellError.output(var, "Type of "+e.getName()+" already defined");
                }
                e.setType(this.type);
            } else {
                HaskellError.output(var,"undefined function");
            }
        }
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new TypeDecl(Copy.deepCol(this.vars),Copy.deep(this.type)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseAddDecl(this);
        hv.fcaseTypeDecl(this);
        this.vars = this.listWalk(this.vars,hv);
        this.type = this.walk(this.type,hv);
        return hv.caseTypeDecl(this);
    }

}
