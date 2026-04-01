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
 * PostCopyVisitor uses the repmap (of PreCopyVsitor) to replace
 * all references to old entities to new entities
 * in the copy of the haskellobjects
 * so the copy only references to new entities
 * (used by modules deepcopy)
 */

public class PostCopyVisitor extends HaskellVisitor {
    Map<HaskellObject,HaskellObject> repMap;
    boolean onevisit;

    //Stack<HaskellObject> last = new Stack<HaskellObject>();

    @Override
    public HaskellObject caseAll(HaskellObject ho){
       HaskellType ht = ho.getTypeTerm();
       if (ht != null) {
           ho.setTypeTerm((HaskellType)ht.visit(this));
       }
       //last.pop();
       return ho;
    }

    @Override
    public void fcaseAll(HaskellObject ho){
        //last.push(ho);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
           //System.out.println(ho.getClass()+"-++-"+ho);
        }

           if (ho instanceof HaskellEntity){

           } else if (ho instanceof HaskellSym) {

           } else if (ho instanceof EntityFrame) {

           } else if (ho instanceof HaskellObject.Visitable){
           }
           //last.pop();

      //  return ho;
    }


    public PostCopyVisitor(Map<HaskellObject,HaskellObject> repMap){
        this.repMap = repMap;
    }

    private HaskellObject repMapGet(HaskellObject ho){
        HaskellObject nho = this.repMap.get(ho);
        if (nho == null) {
            return ho;
        }
        return nho;
    }

    public void entityFrameVisit(EntityFrame ho){
        if (ho instanceof EntityFrame.EntityFrameSkeleton) {
           ((EntityFrame.EntityFrameSkeleton)ho).setParentEntityFrame((EntityFrame)this.repMapGet(((EntityFrame.EntityFrameSkeleton)ho).getParentEntityFrame()));
        } else {
           throw new RuntimeException("djsfhjadfgfj");
        }
        this.onevisit = true;
        ho.visit(this);
    }

    public void entityVisit(HaskellEntity ho){
        ho.setParentEntity((HaskellEntity)this.repMapGet(ho.getParentEntity()));
        ho.setModule((Module)this.repMapGet(ho.getModule()));
        this.onevisit = true;
        ho.visit(this);
    }

    public void normalVisit(HaskellObject ho){
        this.onevisit = false;
        ho.visit(this);
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
        boolean oo = this.onevisit;
        this.onevisit = false;
        return oo;
    }

    @Override
    public boolean guardEntityFrame(EntityFrame ho)             {
        boolean oo = this.onevisit;
        this.onevisit = false;
        return oo;
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


