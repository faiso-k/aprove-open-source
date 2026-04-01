package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * convenience for ImpSpec
 */
public class EntityFilter{

   /**
    * keeps only entities in the set which are in the imports
    */
    public static void matchFilterByImports(Set<HaskellEntity> entities,List<? extends HaskellImport> imports){
        Iterator<HaskellEntity> it = entities.iterator();
        filterLoop: while (it.hasNext()){
            HaskellEntity e = it.next();
            for (HaskellImport imp : imports){
                if (imp.matchFilter(e)){
                    continue filterLoop;
                }
            }
            it.remove();
        }
    }

    /**
     * removes entities form the set which are hidden by the given imports
     */
    public static void hidingFilterByImports(Set<HaskellEntity> entities,List<? extends HaskellImport> imports){
        Iterator<HaskellEntity> it = entities.iterator();
        filterLoop: while (it.hasNext()){
            HaskellEntity e = it.next();
            for (HaskellImport imp : imports){
                if (imp.hidingFilter(e)){
                    it.remove();
                    continue filterLoop;
                }
            }
        }
    }

}
