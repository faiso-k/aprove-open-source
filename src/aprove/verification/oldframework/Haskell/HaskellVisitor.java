package aprove.verification.oldframework.Haskell;

import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The HaskellVisitor is the basic algorithm structure of the whole Haskell framework
 * the most operations are controlled by a specialized visitor.
 *
 * Each object knows which subobjects are available. Each HaskellObject has to overwrite
 * the method visit, to permit access to a visitor. To grand flexibility in each step of
 * execution guards are also added to the standard visitor concept. If and only if a guard
 * methods returns true the proper subobject of an HaskellObject is visited.
 *
 * There are a few named conventions, visitor methods starting with the prefix:
 *  "fcase" are the first case in a HaskellObject, they should be called
 *    directly after the visit methode of a HaskellObject is entered </br>
 *  "icase" are somewhere in the middle of the visit methode, but before </br>
 *  "iicase" are somewhere in the middle of the visit methode, but before </br>
 *  "iiicase" are somewhere in the middle of the visit methode, but before </br>
 *  "case" are the last methods called in a in the methode visit, and thier
 *    return value should be the return value of visit, so every HaskellObject
 *    could be replaced by another one, but the parent object's view to it
 *    has to be COMPATIBLE with the new object.</br>
 *
 *  ...
 *  "guard" are guard methods of subobjects in the visit methode, the could occure
 *        every where in visit. </br>
 *  "outerGuard" are guard methods of the whole object, no other visitor methode
 *               is called if that methode returns false;
 *
 *
 * It seems a bit overkill, but sometimes it was very usefull that
 * a HaskellVisitor is also visitable.
 *
 */

public abstract class HaskellVisitor extends HaskellObject.Visitable {

    public void fcaseEntity(HaskellEntity ho){}
    public void fcaseClassConstraint(ClassConstraint ho){ };
    public void fcaseQuantor(Quantor ho){ };
    public void fcaseTypeSchema(TypeSchema ho){ };
    public void fcaseAddDecl(AddDecl ho) { }
    public void fcaseLetExp(LetExp ho){ }
    public void fcaseLambdaExp(LambdaExp ho){ }
    public void fcaseQuantorExp(QuantorExp ho){ }
    public void fcaseAltExp(AltExp ho){ }
    public void fcaseIrrPat(IrrPat ho){ }
    public void fcaseAtom(Atom ho){}
    public void fcaseApply(Apply ho){}
    public void fcaseFunction(Function ho){}
    public void fcaseIfExp(IfExp ho) { }
    public void fcaseEntityFrame(EntityFrame ho){}
    public void fcaseModule(Module ho){}
    public void fcaseVar(Var ho){}
    public void fcaseCons(Cons ho){}
    public void fcaseCondStackExp(CondStackExp ho){}
    public void fcaseClassDecl(ClassDecl ho){}
    public void fcaseInstDecl(InstDecl ho){}
    public void fcaseDataDecl(DataDecl ho){}
    public void fcaseDataCon(DataCon ho){}
    public void fcaseFieldDecl(FieldDecl ho){}
    public void fcaseInstFunction(InstFunction ho){}
    public void fcaseDefaultDecl(DefaultDecl ho){}
    public void fcaseSynTypeDecl(SynTypeDecl ho){}
    public void fcasePreType(HaskellPreType ho) {}
    public void fcaseCaseExp(CaseExp ho) {}
    public void fcaseHaskellRule(HaskellRule ho) {}
    public void fcaseStartTerms(Modules ho)      {}

    public void fcaseLabCons(LabCons ho) {}
    public void fcaseLabUpdate(LabUpdate ho) {}

    public void fcaseTypeDecl(TypeDecl ho) { }
    public void fcaseFuncDecl(FuncDecl ho) { }
    public void fcasePatDecl(PatDecl ho) { }
    public void fcaseInfixDecl(InfixDecl ho) { }
    public void fcaseHaskellSym(HaskellSym ho) { }
    public void fcaseHaskellNamedSym(HaskellNamedSym ho) { }
    public void fcasePreFunction(PreFunction ho) { }

    public boolean outerGuardApply(Apply ho)                { return true; }

    public boolean guardDefType(SynTypeDecl ho)             { return true; }
    public boolean guardDataType(DataDecl ho)               { return false;}
    public boolean guardConss(DataDecl ho)                  { return true; }
    public boolean guardEntity(HaskellEntity ho)            { return true; }
    public boolean guardEntities(Module ho)                 { return true; }
    public boolean guardValue(HaskellEntity ho)             { return true; }
    public boolean guardType(HaskellEntity ho)              { return true; }
    public boolean guardMember(HaskellEntity ho)            { return true; }
    public boolean guardTypeSchemaTypeExp(TypeExp ho)       { return false;}
    public boolean guardTypeTypeExp(TypeExp ho)             { return true; }
    public boolean guardDecls(TTDecl ho)                    { return true; }
    public boolean guardArguments(HaskellRule ho)           { return true; }
    public boolean guardLetFrame(LetExp ho)                 { return true; }
    public boolean guardLetExpDecl(LetExp ho)               { return false;}
    public boolean guardPatDeclMembers(PatDeclEntity ho)    { return false;}
    public boolean guardPatDecl(PatDecl ho)                 { return true; }
    public boolean guardPatDeclSymbol(PatDecl ho)           { return false;}
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) { return false;}
    public boolean guardDerivings(DataDecl ho)              { return false;}
    public boolean guardModuleFullVisit(Module ho)          { return false;}

    public boolean guardStartTerms(Modules ho)                  { return false;}
    public boolean guardTypeRules(Modules ho)                   { return false;}
    public boolean guardAssumptions(Modules ho)                 { return false;}
    public boolean guardAssumptionEntities(Assumptions ho)      { return false;}
    public boolean guardAltExpEntityFrame(AltExp ho)            { return false;}
    public boolean guardLambdaExpEntityFrame(LambdaExp ho)      { return false;}
    public boolean guardQuantorExpEntityFrame(QuantorExp ho)    { return false;}
    public boolean guardLetExpEntityFrame(LetExp ho)            { return false;}
    public boolean guardPreTypeEntityFrame(HaskellPreType ho)   { return false;}
    public boolean guardHaskellRuleEntityFrame(HaskellRule ho)  { return false;}
    public boolean guardClassDeclEntityFrame(ClassDecl ho)      { return false;}
    public boolean guardInstDeclEntityFrame(InstDecl ho)        { return false;}
    public boolean guardDataDeclEntityFrame(DataDecl ho)        { return false;}
    public boolean guardSynTypeDeclEntityFrame(SynTypeDecl ho)  { return false;}
    public boolean guardFuncDeclEntityFrame(FuncDecl ho)        { return false;}
    public boolean guardEntityFrame(EntityFrame ho)             { return true; }
    public boolean guardDerivedInstEntity(DerivedInstEntity ho) { return false;}
    public boolean guardQuantor(Quantor ho)                     { return false;}
    public boolean guardQuantorExpVars(QuantorExp ho)           { return true; }
    public boolean guardPlusPat(PlusPat ho)                     { return true; }
    public boolean guardBindPat(BindPat ho)                     { return true; }
    public boolean guardMemberTypeSchemaClassConstraint(MemberTypeSchema ho) { return false; }
    public boolean guardDataConTypes(DataCon ho)                { return false;}
    public boolean guardCondStackConditions(CondStackExp ho)    { return true; }
    public boolean guardHaskellRulePatterns(HaskellRule ho)     { return true; }
    public boolean guardFieldDeclEntityFrame(FieldDecl ho)      { return false;}

    public void icaseIfExp(IfExp ho) { }
    public void icaseStartTerms(Modules ho)      {}
    public void icaseHaskellRule(HaskellRule ho) {}
    public void icaseFuncDecl(FuncDecl ho) { }
    public void icaseLetExp(LetExp ho) { }
    public void icaseLambdaExp(LambdaExp ho) { }
    public void icaseQuantorExp(QuantorExp ho) { }
    public void icaseAltExp(AltExp ho) { }
    public void icasePatDecl(PatDecl ho) { }
    public void icaseClassDecl(ClassDecl ho){}
    public void icaseInstDecl(InstDecl ho){}
    public void icaseDataDecl(DataDecl ho) { }
    public void iicaseIfExp(IfExp ho) { }
    public void iicaseClassDecl(ClassDecl ho){}
    public void iicaseInstDecl(InstDecl ho){}
    public void iicaseDataDecl(DataDecl ho) { }
    public void icaseSynTypeDecl(SynTypeDecl ho){}
    public void icasePreType(HaskellPreType ho) {}
    public void icaseEntityFrame(EntityFrame ho){}

    public HaskellObject casePatLambdaExp(PatLambdaExp ho){ return ho; }
    public HaskellObject caseEntityFrame(EntityFrame ho){ return ho; }
    public HaskellObject caseEntity(HaskellEntity ho){ return ho; }
    public HaskellObject caseQuantor(Quantor ho){ return ho; };
    public HaskellObject caseClassConstraint(ClassConstraint ho){ return ho; };
    public HaskellObject caseTypeSchema(TypeSchema ho){ return ho; };
    public HaskellObject caseModule(Module ho){ return ho; }
    public HaskellObject caseVar(Var ho){return ho;}
    public HaskellObject caseIrrPat(IrrPat ho){return ho;}
    public HaskellObject caseBindPat(BindPat ho){return ho;}
    public HaskellObject casePlusPat(PlusPat ho){return ho;}
    public HaskellObject caseJokerPat(JokerPat ho){return ho;}
    public HaskellObject caseCons(Cons ho){return ho;}
    public HaskellObject caseAll(HaskellObject ho){ return ho; }
    public void fcaseAll(HaskellObject ho){ }
    public HaskellObject caseOperator(Operator ho){ return ho; }
    public HaskellObject caseRawTerm(RawTerm ho){ return ho; }
    public HaskellObject caseLetExp(LetExp ho){ return ho; }
    public HaskellObject caseLambdaExp(LambdaExp ho){ return ho; }
    public HaskellObject caseQuantorExp(QuantorExp ho){ return ho; }
    public HaskellObject caseApply(Apply ho){ return ho; }
    public HaskellObject caseAltExp(AltExp ho){ return ho; }
    public HaskellObject caseTypeExp(TypeExp ho){ return ho; }
    public HaskellObject caseCaseExp(CaseExp ho){ return ho; }
    public HaskellObject caseCondExp(CondExp ho){ return ho; }
    public HaskellObject caseCondStackExp(CondStackExp ho){ return ho; }
    public HaskellObject caseHaskellRule(HaskellRule ho){ return ho; }
    public HaskellObject caseFunction(Function ho){ return ho; }

    public HaskellObject caseLabCons(LabCons ho){ return ho; }
    public HaskellObject caseLabUpdate(LabUpdate ho){ return ho; }

    public HaskellObject caseTypeDecl(TypeDecl ho) { return ho; }
    public HaskellObject caseFuncDecl(FuncDecl ho) { return ho; }
    public HaskellObject casePatDecl(PatDecl ho) { return ho; }
    public HaskellObject caseIfExp(IfExp ho) { return ho; }
    public HaskellObject caseHaskellSym(HaskellSym ho) { return ho; }
    public HaskellObject caseHaskellNamedSym(HaskellNamedSym ho) { return ho; }
    public HaskellObject casePreFunction(PreFunction ho) { return ho; }
    public HaskellObject casePreType(HaskellPreType ho) { return ho; }
    public HaskellObject caseClassDecl(ClassDecl ho){ return ho;}
    public HaskellObject caseInstDecl(InstDecl ho){ return ho;}
    public HaskellObject caseDataDecl(DataDecl ho){ return ho;}
    public HaskellObject caseDataCon(DataCon ho){ return ho;}
    public HaskellObject caseFieldDecl(FieldDecl ho) { return ho;}
    public HaskellObject caseSynTypeDecl(SynTypeDecl ho){ return ho;}
//    public HaskellObject casePatDeclValue(PatDeclValue ho) { return ho;}

    public HaskellObject caseCharLit(CharLit ho) { return ho;}
    public HaskellObject caseFloatLit(FloatLit ho) { return ho;}
    public HaskellObject caseIntegerLit(IntegerLit ho) { return ho;}

    @Override
    public HaskellObject deepcopy(){
        return this;
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        return this;
    }
}


