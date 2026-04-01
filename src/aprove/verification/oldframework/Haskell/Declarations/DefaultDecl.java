package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * Ths class represents the default declaration of Haskell, only one per module is allowed
 */
public class DefaultDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl, HaskellBean {
    Module module;
    List<Cons> types;

    /**
     * do not use this constructor, its only for bean convention
     */
    public DefaultDecl(){
    }

    public DefaultDecl(List<Cons> types){
        this.types = types;
    }

    public List<Cons> getTypes(){
        return this.types;
    }

    public void setTypes(List<Cons> types){
        this.types = types;
    }

    public void addToModule(){
        this.module.setDefaultList(this.types);
    }

    public void setModule(Module module){
        this.module = module;
    }

    public Module getModule(){
        return this.module;
    }

    @Override
    public Object deepcopy(){
        DefaultDecl dd = new DefaultDecl(Copy.deepCol(this.types));
        dd.setModule(this.module);
        return this.hoCopy(dd);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseDefaultDecl(this);
        this.types = this.listWalk(this.types,hv);
        return this;
    }

}
