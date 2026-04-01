package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.HaskellProblem.Processors.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Typing.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * Reductions are basically HaskellVisitors
 * an this class is the base class for the standard reductions
 * it offers some convenience like:
 * current Module, current Function, function stack, ....
 */
public class BasicReduction extends HaskellVisitor {
    Abortion aborter;

    Stack<EntityFrame> entityFrames = new Stack<EntityFrame>();
    Stack<Function> functions = new Stack<Function>();
    Stack<List<HaskellEntity>> currentCollects = new Stack<List<HaskellEntity>>();
    HaskellProof hp;

    boolean changeFlag = false;
    boolean nullCheck = false;

    Prelude prelude;
    Module curModule;
    Module mainModule;
    Modules curModules;

    public void setAborter(Abortion aborter){
        this.aborter = aborter;
    }

    public void setHaskellProof(HaskellProof hp){
        this.hp = hp;
    }

    public void proofAdd(Object a,Module ma,Object b,Module mb){
        this.hp.add(a,ma,b,mb);
    }

    public <T> T checkNull(T obj){
        this.nullCheck = obj == null || this.nullCheck;
        return obj;
    }

    public String getNextNewNameFromFunction(){
         String name = null;
         if (this.functions.size()==0) {
             name = "startTerm";
         } else {
             Function curFunc = this.functions.peek();
             name = curFunc.getSymbol().getName(false);
         }
         return this.prelude.getNextNameFor(name);
    }

    public String getNextNewNameForVariable(){
         return this.prelude.buildUniqueName();
    }

    public Function getCurFunction(){
         return this.functions.peek();
    }

    public Module getCurModule(){
         return this.curModule;
    }

    public Modules getCurModules(){
         return this.curModules;
    }

    public EntityFrame getCurEntityFrame(){
         return this.entityFrames.peek();
    }

    public void addToEntityFrame(HaskellEntity entity){
         this.currentCollects.peek().add(entity);
    }

    private void popCurrenctCollects(){
        EntityFrame entityFrame = this.entityFrames.peek();
        for (HaskellEntity e : this.currentCollects.peek()){
             entityFrame.addEntity(e);
        }
        this.currentCollects.pop();
    }

    public boolean wasChanged(){
        return this.changeFlag;
    }

    public void setChanged(){
        this.changeFlag = true;
    }

    public Set<ClassConstraint> getCurrentConstraints(HaskellType type) {
        Set<ClassConstraint> ccs = new HashSet<ClassConstraint>();

        for(Function f : this.functions) {
            ccs.addAll(this.curModules.getAssumptions().getTypeSchemaFor(f.getSymbol().getEntity()).getConstraints());
        }

        this.curModules.reduceConstraintsBy(ccs, type);

        return ccs;
    }

    public void createAssumptionFor(Function func, Set<ClassConstraint> ccs){
        HaskellEntity e = func.getSymbol().getEntity();
        HaskellRule rule = func.getRules().iterator().next();
        List<HaskellType> hts = HaskellTools.getTypeTerms(rule.getPatterns());
        hts.add(rule.getExpression().getTypeTerm());
        TypeSchema ts = TypeSchema.create(ccs,(HaskellType)this.prelude.buildArrows(hts));
        this.curModules.getAssumptions().pushAssumption(e,ts);
    }

    public void createAssumptionFor(Function func){
        HaskellEntity e = func.getSymbol().getEntity();
        HaskellRule rule = func.getRules().iterator().next();
        List<HaskellType> hts = HaskellTools.getTypeTerms(rule.getPatterns());
        hts.add(rule.getExpression().getTypeTerm());
        HaskellType newType = (HaskellType)this.prelude.buildArrows(hts);
        TypeSchema ts = TypeSchema.create(this.getCurrentConstraints(newType),newType);
        ts.autoQuantor();
        this.curModules.getAssumptions().pushAssumption(e,ts);
    }



    @Override
    public void fcaseLetExp(LetExp ho){
        this.entityFrames.push(ho.getEntityFrame());
        this.currentCollects.push(new Vector<HaskellEntity>());
    }

    @Override
    public HaskellObject caseLetExp(LetExp ho){
        this.popCurrenctCollects();
        this.entityFrames.pop();
        return ho;
    }

    @Override
    public void fcaseFunction(Function ho){
        this.functions.push(ho);
    }

    @Override
    public HaskellObject caseFunction(Function ho){
        this.functions.pop();
        return ho;
    }

    @Override
    public void fcaseModule(Module ho){
        this.curModule = ho;
        this.entityFrames.push(ho);
        this.currentCollects.push(new Vector<HaskellEntity>());
    }

    @Override
    public Module caseModule(Module ho){
        this.curModule = ho;
        this.popCurrenctCollects();
        this.entityFrames.pop();
        return ho;
    }

    public void forModules(Modules modules){
        this.prelude = modules.getPrelude();
        this.mainModule = modules.getMainModule();
        this.curModules = modules;
        modules.visit(this);
    }

    @Override
    public void fcaseStartTerms(Modules ho){
        this.curModule = this.mainModule;
        this.entityFrames.push(this.curModule);
        this.currentCollects.push(new Vector<HaskellEntity>());
    }

    @Override
    public void icaseStartTerms(Modules ho){
        this.curModule = this.mainModule;
        this.popCurrenctCollects();
        this.entityFrames.pop();
    }


    @Override
    public boolean guardStartTerms(Modules ho)         { return true; }
    @Override
    public boolean guardEntities(Module ho)            { return true; }
    @Override
    public boolean guardDefType(SynTypeDecl ho)        { return false;}
    @Override
    public boolean guardDataType(DataDecl ho)          { return false;}
    @Override
    public boolean guardConss(DataDecl ho)             { return false;}
    @Override
    public boolean guardEntity(HaskellEntity ho)       { return true;}
    @Override
    public boolean guardValue(HaskellEntity ho)        { return true;}
    @Override
    public boolean guardType(HaskellEntity ho)         { return false;}
    @Override
    public boolean guardMember(HaskellEntity ho)       { return true;}
    @Override
    public boolean guardTypeTypeExp(TypeExp ho)        { return false;}
    @Override
    public boolean guardDecls(TTDecl ho)               { return false;}
    @Override
    public boolean guardArguments(HaskellRule ho)      { return false;}
    @Override
    public boolean guardLetFrame(LetExp ho)            { return true;}
    @Override
    public boolean guardPatDecl(PatDecl ho)            { return false;}
    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) { return false;}
    public boolean oguardApply(Apply ho)                { return true; }
    @Override
    public boolean guardDerivings(DataDecl ho)         {  return false; }

}
