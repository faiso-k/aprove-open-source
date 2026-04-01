package aprove.verification.oldframework.Haskell.Declarations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The ImpDecl represent the import statememt of Haskell, it contains
 * the module alias and a link to the module.
 * HaskellBean
 */
public class ImpDecl extends HaskellObject.HaskellObjectSkeleton implements HaskellDecl,HaskellBean {
    HaskellSym module; // the module the import refers to
    HaskellSym alias; // the module alias
    ImpSpec impSpec; // import list
    boolean quali; // is the import qaulified or not

    /**
     * do not use this constructor only for bean convention
     */
    public ImpDecl(){
    }

    /**
     *  use this constructor
     */
    public ImpDecl(boolean quali,HaskellSym module,HaskellSym alias,ImpSpec impSpec){
        this.quali = quali;
        this.module = module;
        this.alias = alias;
        this.impSpec = impSpec;
    }

    public boolean getQuali(){
        return this.quali;
    }

    public void setQuali(boolean quali){
        this.quali = quali;
    }

    public ImpSpec getImpSpec(){
        return this.impSpec;
    }

    public void setImpSpec(ImpSpec impSpec){
        this.impSpec = impSpec;
    }

    public HaskellSym getModule(){
        return this.module;
    }

    public void setModule(HaskellSym module){
        this.module = module;
    }

    public HaskellSym getAlias(){
        return this.alias;
    }

    public void setAlias(HaskellSym alias){
        this.alias = alias;
    }

    public String getImportModule(){
        return this.module.getName(true);
    }

    public String getAliasQualifier(){
        if (this.alias == null) {
            return this.getImportModule();
        }
        return this.alias.getName(true);
    }

    public boolean isQualified(){
        return this.quali;
    }

    /**
     * @return all entities that are imported by this import statement
     * by consideration of the export list of the module this impdecl refers to
     * therefore the current module set (modules) is needed
     */
    public Set<HaskellEntity> getImportEntities(Modules modules){
        Set<HaskellEntity> res = new HashSet<HaskellEntity>(modules.getExportEntitiesFor(this.getImportModule()));
        if (this.impSpec != null) { this.impSpec.filter(res); }
        return res;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new ImpDecl(this.quali,Copy.deep(this.module),Copy.deep(this.alias),Copy.deep(this.impSpec)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.module = this.walk(this.module,hv);
        this.alias = this.walk(this.alias,hv);
        this.impSpec = this.walk(this.impSpec,hv);
        return this;
    }

}
