package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Syntax.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The PreTypeToSchemaVisitor transformes the pretypes to typeschemata
 * it works through all type-containing HaskellObjects
 */
public class PreTypeToSchemaVisitor extends HaskellVisitor {
    Set <HaskellEntity.Sort> VALUESOF = EnumSet.of(HaskellEntity.Sort.VAR,
                                                   HaskellEntity.Sort.IVAR,
                                                   HaskellEntity.Sort.TYCONS,
                                                   HaskellEntity.Sort.PATDECL);

    Set <HaskellEntity.Sort> TYPESOF  = EnumSet.of(HaskellEntity.Sort.CONS,
                                                   HaskellEntity.Sort.VAR,
                                                   HaskellEntity.Sort.IVAR);

    Set <HaskellEntity> already  = new HashSet<HaskellEntity>();
    Set <HaskellBasicRule> typeRules;

    public PreTypeToSchemaVisitor(Set<HaskellBasicRule> typeRules){
        this.typeRules = typeRules;
    }

    @Override
    public boolean guardValue(HaskellEntity ho){
        return this.VALUESOF.contains(ho.getSort());
    }

    @Override
    public boolean guardEntity(HaskellEntity ho){
        if (this.already.contains(ho)) {
            return false;
        }
        this.already.add(ho);
        return true;
    }

    @Override
    public boolean guardType(HaskellEntity ho){
        return this.TYPESOF.contains(ho.getSort());
    }

    @Override
    public boolean guardDataType(DataDecl ho){
        return true;
    }

    @Override
    public boolean guardMember(HaskellEntity ho){
        return true;
    }

    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) {
        return true;
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

    @Override
    public HaskellObject casePreType(HaskellPreType ho) {
        return ho.toTypeSchema(this.typeRules);
    }

    @Override
    public HaskellObject caseTypeExp(TypeExp ho) {
        ho.buildTypeSchema(this.typeRules);
        return ho;
    }

    @Override
    public boolean guardTypeTypeExp(TypeExp ho) {
        return false;
    }

}
