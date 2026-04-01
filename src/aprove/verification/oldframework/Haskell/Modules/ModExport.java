package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * A ModExport represents a Module export in the export list of a Haskell Program.
 */
public class ModExport extends SymObject implements HaskellExport,HaskellBean {

    /**
     * do not use this constructor, its only for bean convention
     */
    public ModExport(){
    }

    /**
     * normal constructor
     */
    public ModExport(HaskellSym sym){
        super(sym);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new ModExport(Copy.deep(this.getSymbol())));
    }

    /**
     * the name of the module which is exported
     */
    public String getExportModule(){
        return this.getSymbol().getName(true);
    }

    /**
     * @return the ExportEntities exported by this ModExport are the
     *         directly reachable (unqualified) imports
     *         if the current module is not meant by this ModExport.
     *         If the current module is meant by this ModExport
     *         only the local entities (top decls, data types,..) are exported.
     */
    @Override
    public Set<HaskellEntity> getExportEntities(Module mod){
        if (mod.getName().equals(this.getExportModule())) {
            return mod.getLocalEntities();
        } else {
            return mod.getImportEntitiesFor(this.getExportModule());
        }
    }

}
