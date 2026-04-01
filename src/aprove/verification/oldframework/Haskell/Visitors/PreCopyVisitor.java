package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 *
 * this visitor copies entities (entityframes) if they are not listed in the repMap
 * and add a new entry for them in the repmap
 * (used by modules deepcopy)
 */

public class PreCopyVisitor extends HaskellVisitor {
    Map<HaskellObject,HaskellObject> repMap;
    List<HaskellEntity> newEntities;
    List<EntityFrame> newEntityFrames;
    Modules newModules;

    public PreCopyVisitor(Map<HaskellObject,HaskellObject> repMap,List<HaskellEntity> newEntities,List<EntityFrame> newEntityFrames,Modules newModules){
        this.repMap = repMap;
        this.newEntities = newEntities;
        this.newEntityFrames = newEntityFrames;
        this.newModules = newModules;
    }

    @Override
    public boolean guardEntity(HaskellEntity ho){
        if (this.repMap.get(ho) == null) {
            // not in repMap, copy the entity and add an entry in the repmap
            HaskellEntity newEntity = Copy.deep(ho);
            this.newEntities.add(newEntity);
            this.repMap.put(ho,newEntity);
            return true;
        }
        return false;
    }

    @Override
    public HaskellObject caseHaskellSym(HaskellSym ho) {
        if (this.repMap.get(ho) == null){
            // not in repMap, create a new HaskellSym for it and add an entry in the repmap
            this.repMap.put(ho,new HaskellSym());
        }
        return ho;
    }

    @Override
    public HaskellObject caseModule(Module ho){
        if (this.repMap.get(ho) == null){
            // not in repMap, so copy the module and add an entry in the repmap
            Module newModule = Copy.deep(ho);
            if (newModule.isPrelude()) {
                this.newModules.setPrelude((Prelude)newModule);
                // for the prelude, register the prelude in the modules
            }
            this.newModules.addModule(newModule); // register each module in the modules
            this.repMap.put(ho,newModule);
        }
        return ho;
    }

    @Override
    public boolean guardEntityFrame(EntityFrame ho){
        if (this.repMap.get(ho) == null){
            // not in repMap, so copy the entityframe and add an entry in the repmap
            EntityFrame.EntityFrameSkeleton newEntityFrame = (EntityFrame.EntityFrameSkeleton) Copy.deep(ho);
            this.newEntityFrames.add(newEntityFrame);
            this.repMap.put(ho,newEntityFrame);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(ho);
            }
        }
        return true;
    }

    @Override
    public boolean guardQuantorExpEntityFrame(QuantorExp ho){ return true; }
    @Override
    public boolean guardStartTerms(Modules ho)              { return true; }
    @Override
    public boolean guardTypeRules(Modules ho)               { return true;}
    @Override
    public boolean guardAssumptions(Modules ho)             { return true;}
    @Override
    public boolean guardAssumptionEntities(Assumptions ho)  { return true; }
    @Override
    public boolean guardDefType(SynTypeDecl ho)             { return true; }
    @Override
    public boolean guardDataType(DataDecl ho)               { return true; }
    @Override
    public boolean guardConss(DataDecl ho)                  { return true; }
    @Override
    public boolean guardEntities(Module ho)                 { return true; }
    @Override
    public boolean guardValue(HaskellEntity ho)             { return true; }
    @Override
    public boolean guardType(HaskellEntity ho)              { return true; }
    @Override
    public boolean guardMember(HaskellEntity ho)            { return true; }
    @Override
    public boolean guardTypeTypeExp(TypeExp ho)             { return true; }
    @Override
    public boolean guardDecls(TTDecl ho)                    { return true; }
    @Override
    public boolean guardArguments(HaskellRule ho)           { return true; }
    @Override
    public boolean guardLetFrame(LetExp ho)                 { return true; }
    @Override
    public boolean guardPatDeclMembers(PatDeclEntity ho)    { return true; }
    @Override
    public boolean guardPatDecl(PatDecl ho)                 { return true; }
    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) { return true; }
    @Override
    public boolean guardDerivings(DataDecl ho)              { return true; }
    @Override
    public boolean guardModuleFullVisit(Module ho)          { return true; }
    @Override
    public boolean guardAltExpEntityFrame(AltExp ho)            { return true;}
    @Override
    public boolean guardLambdaExpEntityFrame(LambdaExp ho)      { return true;}
    @Override
    public boolean guardLetExpEntityFrame(LetExp ho)            { return true;}
    @Override
    public boolean guardPreTypeEntityFrame(HaskellPreType ho)   { return true;}
    @Override
    public boolean guardHaskellRuleEntityFrame(HaskellRule ho)  { return true;}
    @Override
    public boolean guardClassDeclEntityFrame(ClassDecl ho)      { return true;}
    @Override
    public boolean guardInstDeclEntityFrame(InstDecl ho)        { return true;}
    @Override
    public boolean guardDataDeclEntityFrame(DataDecl ho)        { return true;}
    @Override
    public boolean guardSynTypeDeclEntityFrame(SynTypeDecl ho)  { return true;}
    @Override
    public boolean guardFuncDeclEntityFrame(FuncDecl ho)        { return true;}
    @Override
    public boolean guardDerivedInstEntity(DerivedInstEntity ho) { return true;}
    @Override
    public boolean guardQuantor(Quantor ho)                     { return true;}
    @Override
    public boolean guardLetExpDecl(LetExp ho)               { return true;}
    @Override
    public boolean guardMemberTypeSchemaClassConstraint(MemberTypeSchema ho) { return true; }
    @Override
    public boolean guardTypeSchemaTypeExp(TypeExp ho)       { return true;}
    @Override
    public boolean guardDataConTypes(DataCon ho)                {return true; }


}


