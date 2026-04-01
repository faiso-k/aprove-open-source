package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor build all the concrete typeschemata for the InstEntities.
 * and IVarEntities by using the typeschemata of the CVarEntities (class members)
 */
public class InstantiationVisitor extends HaskellVisitor {
    Set<HaskellEntity.Sort> INSTANCES = EnumSet.of(HaskellEntity.Sort.INST,
                                                   HaskellEntity.Sort.IVAR);

    Set<HaskellEntity> already  = new HashSet<HaskellEntity>();

    @Override
    public boolean guardValue(HaskellEntity ho){
        return false;
    }

    @Override
    public boolean guardEntity(HaskellEntity ho){
        if (ho.getSort()== HaskellEntity.Sort.INST) {
           ((InstEntity)ho).instantiate();
        }
        if (!this.INSTANCES.contains(ho.getSort())) {
            return false;
        }
        if (this.already.contains(ho)) {
            return false;
        }
        if (ho.getSort()== HaskellEntity.Sort.IVAR) {
           ((IVarEntity)ho).instantiate();
        }
        this.already.add(ho);
        return true;
    }

    @Override
    public boolean guardType(HaskellEntity ho){
        return false;
    }

    @Override
    public boolean guardMember(HaskellEntity ho){
        return ho.getSort() == HaskellEntity.Sort.INST;
    }

    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) {
        return false;
    }

    @Override
    public boolean guardConss(DataDecl ho){
        return false;
    }

    @Override
    public boolean guardDefType(SynTypeDecl ho){
        return false;
    }

    @Override
    public boolean guardDecls(TTDecl ho){
        return false;
    }

}
