package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor is only for debug reasons implemented do not use it
 * for other purpose.
 */

public class PostPostCopyVisitor extends HaskellVisitor {
    Set<HaskellEntity> vis = new HashSet<HaskellEntity>();

    Map<HaskellObject,HaskellObject> repMap;
    List<HaskellEntity> newEntities;
    List<EntityFrame> newEntityFrames;
    Modules newModules;
    boolean copy;
    Stack<HaskellObject> last = new Stack<HaskellObject>();

    @Override
    public HaskellObject caseAll(HaskellObject ho){
            if (this.copy){
        }else {
       this.last.pop();
       }
       return ho;
    }
    @Override
    public void fcaseAll(HaskellObject ho){
            if (this.copy){
        }else {
           this.last.push(ho);

           // XXX DEBUG
           if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
               //System.out.println(ho.getClass()+"----"+ho);
           }

           if (ho instanceof HaskellObject.Visitable){
/*              if (((HaskellObject.Visitable)ho).flag >0) {
                  HaskellSym.showee(last);
                  throw new RuntimeException("scfghdsgfdashfhj");
              }*/
           }
           //last.pop();
        }
      //  return ho;
    }

    public PostPostCopyVisitor(boolean copy,Map<HaskellObject,HaskellObject> repMap,List<HaskellEntity> newEntities,List<EntityFrame> newEntityFrames,Modules newModules){
        this.repMap = repMap;
        this.newEntities = newEntities;
        this.newEntityFrames = newEntityFrames;
        this.newModules = newModules;
        this.copy = copy;
    }



    private HaskellObject repMapGet(HaskellObject ho){
        return ho;
    }


    @Override
    public HaskellObject caseHaskellSym(HaskellSym ho) {
        return this.repMapGet(ho);
    }

    @Override
    public HaskellObject caseModule(Module ho){
        return this.repMapGet(ho);
    }

    @Override
    public HaskellObject caseEntityFrame(EntityFrame ho){
        return this.repMapGet(ho);
    }

    @Override
    public HaskellObject caseEntity(HaskellEntity ho){
        return this.repMapGet(ho);
    }

    @Override
    public boolean guardEntity(HaskellEntity ho)                {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println(" "+ho.getClass()+":"+ho+"--"+((HaskellEntity.Skeleton) ho).num);
        }

        if (this.vis.contains(ho)) {
          if (this.copy) {
            if (((HaskellEntity.HaskellEntitySkeleton) ho).num< 2374) {
               HaskellSym.showee(ho);
               HaskellSym.showee(this.repMap.get(ho));
               throw new RuntimeException("copy dddddddddddddddddddddddddddd");
            }
            return false;
          } else {
            if (((HaskellEntity.HaskellEntitySkeleton) ho).num> 2373) {
               HaskellSym.showee(ho);
               HaskellSym.showee(this.repMap.get(ho));
               throw new RuntimeException("nocopy dddddddddddddddddddddddddddd");
            }
            return false;
          }
        }
        if (ho != null) {
            if (ho.getModule().getModules() != this.newModules){
                System.out.println("PPCV: "+ho+"; "+ho.getClass());
            }
        }
        this.vis.add(ho);
        return true;
    }

    @Override
    public boolean guardEntityFrame(EntityFrame ho)             {
        if (this.copy) {
/*        if (((EntityFrame.Skeleton)ho).flag < 30) {
              HaskellSym.showee(ho);
              HaskellSym.showee(repMap.get(ho));
              throw new RuntimeException("copy frame");
        }
        } else {
        if (((EntityFrame.Skeleton)ho).flag > 29) {
              HaskellSym.showee(ho);
              HaskellSym.showee(repMap.get(ho));
              throw new RuntimeException("nocopy frame");
        }        */
        }
        return true;
    }

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

}


