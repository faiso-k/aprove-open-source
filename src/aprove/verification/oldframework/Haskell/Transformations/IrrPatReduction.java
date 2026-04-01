package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.HaskellProblem.Processors.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * it is only korrekt (korega tabs) if it is applied befor the binding reduction is applied !!!!
 */
public class IrrPatReduction extends BasicReduction {
    Stack<ReductionFrame> stack = new Stack<ReductionFrame>();

    private HaskellExp reduceIrr(IrrPat ip) {
         Module curModule = this.getCurModule();

         List<Var> freeVars = new Vector<Var>();
         ip.visit(new FreeLocalVarCollector(freeVars));
         HaskellPat pat = ip.getPattern();
         Set<HaskellObject> neededSet = new LinkedHashSet<HaskellObject>();
         String name = this.getNextNewNameForVariable();
         VarEntity newVarEntity = new VarEntity(name,curModule,null,null,true);
         this.stack.peek().addEntity(newVarEntity); // localframe new Var
         for (Var var : freeVars){
             HaskellEntity e = var.getSymbol().getEntity();
             Var funcVar = this.createFunctionEntity(var,pat,freeVars);
             Var newVar = new Var(new HaskellNamedSym(newVarEntity));
             newVar.setTypeTerm(pat.getTypeTerm());
             // z -> ... f_e z ...
             this.stack.peek().putVarRep(e,this.prelude.buildApply(funcVar,newVar));
             this.stack.peek().removeEntity(e); // localframe without freeVarEntities
             this.addToEntityFrame(funcVar.getSymbol().getEntity());    // add function to letframe
             neededSet.add(funcVar.getSymbol().getEntity());
         }
         this.proofAdd(ip,curModule,neededSet,curModule);
         return (HaskellExp)(new Var(new HaskellNamedSym(newVarEntity))).setTypeTerm(pat.getTypeTerm());
     }

     private Var createFunctionEntity(Var curVar,HaskellPat pat,List<Var> freeVars){
         Module curModule = this.getCurModule();
         EntityFrame curEntityFrame = this.getCurEntityFrame();

         // new EntityFrame and Entity Replacemap
         EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(curEntityFrame,new EntityMap());
         Map<HaskellEntity,HaskellObject> mapE2V = new HashMap<HaskellEntity,HaskellObject>();
         for(Var var : freeVars){
              HaskellEntity entity = var.getSymbol().getEntity();
              HaskellEntity newEntity = new VarEntity(entity.getName(),curModule,null,null,true);
              eframe.addEntity(newEntity);
              Var newVar = new Var(new HaskellNamedSym(newEntity));
              newVar.setTypeTerm(var.getTypeTerm());
              mapE2V.put(entity,newVar);
         }

         // new Rule  f pat -> exp
         VarEntitySubstitutor fes = new VarEntitySubstitutor(mapE2V);
         List<HaskellPat> pats = new Vector<HaskellPat>();
         pat = (HaskellPat) Copy.deep(pat);
         pat = (HaskellPat) pat.visit(fes);
         pats.add(pat);
         curVar = (Var) curVar.visit(fes);
         HaskellType ruleType = this.prelude.buildArrow(pat.getTypeTerm(),curVar.getTypeTerm());

         // new Rules
         HaskellRule newRule = new HaskellRule(eframe,pats,curVar);
         List<HaskellRule> newRules = new Vector<HaskellRule>();
         newRule.setTypeTerm(ruleType);
         newRules.add(newRule);

         // new Function
         String newName = this.getNextNewNameFromFunction();
         VarEntity newVarEntity = new VarEntity(newName,curModule,null,null);
         Function newFunction = new Function(new HaskellNamedSym(newVarEntity),newRules);
         newVarEntity.setValue(newFunction);
         this.createAssumptionFor(newFunction);
         newFunction.setTypeTerm(ruleType);
         return (Var)(new Var(new HaskellNamedSym(newVarEntity))).setTypeTerm(ruleType);
    }

    @Override
    public HaskellObject caseIrrPat(IrrPat ho) {
        this.setChanged();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("IrrPar Reduction: replace");
        }

        return this.reduceIrr(ho);
    }

    public void pushStack(){
         this.stack.push(new ReductionFrame());
    }

    public ReductionFrame popStack(){
         return this.stack.pop();
    }

    @Override
    public void fcaseLambdaExp(LambdaExp ho){
       this.pushStack();
    }

    @Override
    public HaskellObject caseLambdaExp(LambdaExp ho){
       this.popStack().replaceAndUpdate(ho);
       return ho;
    }

    @Override
    public void fcaseAltExp(AltExp ho){
       this.pushStack();
    }

    @Override
    public HaskellObject caseAltExp(AltExp ho){
       this.popStack().replaceAndUpdate(ho);
       return ho;
    }

    @Override
    public void fcaseHaskellRule(HaskellRule ho){
       this.pushStack();
    }

    @Override
    public HaskellObject caseHaskellRule(HaskellRule ho){
       this.popStack().replaceAndUpdate(ho);
       return ho;
    }

    public static boolean applyTo(Modules modules,HaskellProof hp,Abortion aborter){
        IrrPatReduction ipr = new IrrPatReduction();
        ipr.setAborter(aborter);
        ipr.setHaskellProof(hp);
        ipr.forModules(modules);
        return ipr.wasChanged();
        //return true;
    }

}
