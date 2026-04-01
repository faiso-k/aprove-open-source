package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * ImpSpec represents an import specification
 */
public class ImpSpec extends HaskellObject.HaskellObjectSkeleton implements HaskellBean{
    boolean hiding;
    List<HaskellImport> imports;

    /**
     * do not use this constructor, its only for bean convention
     */
    public ImpSpec(){
    }

    /**
     * normal constructor
     */
    public ImpSpec(boolean hiding,List<HaskellImport> imports){
        this.hiding = hiding;
        this.imports = imports;
    }

    public void setHiding(boolean hiding){
        this.hiding = hiding;
    }

    public boolean getHiding(){
        return this.hiding;
    }

    public void setImports(List<HaskellImport> imports){
        this.imports = imports;
    }

    public List<HaskellImport> getImports(){
        return this.imports;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new ImpSpec(this.hiding,Copy.deepCol(this.imports)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.imports = this.listWalk(this.imports,hv);
        return this;
    }

    /**
     * filters entities by this import specification
     */
    public void filter(Set<HaskellEntity> entities){
       if (this.hiding){
           EntityFilter.hidingFilterByImports(entities,this.imports);
       } else {
           EntityFilter.matchFilterByImports(entities,this.imports);
       }
    }

}
