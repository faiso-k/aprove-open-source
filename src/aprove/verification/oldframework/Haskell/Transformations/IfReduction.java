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
 *
 * IfReduction reduces the if structure of Haskell to a new function
 * and adds a call of this function.
 */
public class IfReduction extends BasicReduction {
    HaskellEntity trueEntity;
    HaskellEntity falseEntity;

    private HaskellEntity getEntity(String name){
        return this.prelude.getEntityN(this,"Prelude",name,HaskellEntity.Sort.CONS);
    }

    private Cons buildCons(HaskellEntity entity){
        Cons bco = new Cons(new HaskellNamedSym(entity));
        Cons bool = new Cons(this.prelude.getBoolSym());
        bco.setTypeTerm(bool);
        return bco;
    }

    private HaskellExp reduce(IfExp ie) {
         Module curModule = this.getCurModule();
         EntityFrame curEntityFrame = this.getCurEntityFrame();
         String newName = this.getNextNewNameFromFunction();
         List<Var> freeVars = new Vector<Var>();
         FreeLocalVarCollector flvc = new FreeLocalVarCollector(freeVars);
         ie.getTrueCase().visit(flvc);
         ie.getFalseCase().visit(flvc);

         VarEntity newVarEntity = new VarEntity(newName,curModule,null,null);
         List<HaskellRule> newRules = new Vector<HaskellRule>();

         List<HaskellType> hts = HaskellTools.getTypeTerms(freeVars);
         hts.add(ie.getCond().getTypeTerm());
         hts.add(ie.getTypeTerm());

         HaskellType ruleType = this.prelude.buildArrows(hts);

         HaskellExp repTerm = new Var(new HaskellNamedSym(newVarEntity));
         repTerm.setTypeTerm(ruleType);

         // XXX DEBUG
         if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
             System.out.println(hts);
             System.out.println(ruleType);
         }

         List<Var> vvv = Copy.deepCol(freeVars);

         // XXX DEBUG
         if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
             System.out.println(vvv);
             System.out.println(HaskellTools.getTypeTerms(vvv));
         }

         repTerm =(HaskellExp) this.prelude.buildApplies(repTerm,vvv);
         repTerm =(HaskellExp) this.prelude.buildApply(repTerm,ie.getCond());

         HaskellExp[] results = new HaskellExp[]{ie.getTrueCase(),ie.getFalseCase()};
         HaskellPat[] cases   = new HaskellPat[]{this.buildCons(this.trueEntity),this.buildCons(this.falseEntity)};
         for(int i=0;i<2;i++){
            List<HaskellPat> pats = new Vector<HaskellPat>();
            EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(curEntityFrame,new EntityMap());
            Map<HaskellEntity,HaskellObject> mapE2V = new HashMap<HaskellEntity,HaskellObject>();
            for(Var var : freeVars){
                 HaskellEntity entity = var.getSymbol().getEntity();
                 HaskellEntity newEntity = new VarEntity(entity.getName(),curModule,null,null,true);
                 eframe.addEntity(newEntity);
                 Var newVar = new Var(new HaskellNamedSym(newEntity));
                 newVar.setTypeTerm(var.getTypeTerm());
                 mapE2V.put(entity,newVar);
                 pats.add(newVar);
            }
            HaskellExp res = results[i];
            res = (HaskellExp) res.visit(new VarEntitySubstitutor(mapE2V));
            pats.add(cases[i]);
            eframe.setParentEntityFrame(curEntityFrame);
            HaskellRule newRule = new HaskellRule(eframe,pats,res);
            newRule.setTypeTerm(ruleType);
            newRules.add(newRule);
         }

         Function newFunction = new Function(new HaskellNamedSym(newVarEntity),newRules);
         newFunction.setTypeTerm(ruleType);
         newVarEntity.setValue(newFunction);
         this.createAssumptionFor(newFunction);
         this.addToEntityFrame(newVarEntity);
         this.proofAdd(ie,curModule,newVarEntity,curModule);
         return repTerm;
    }

    @Override
    public HaskellObject caseIfExp(IfExp ho) {
        this.setChanged();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("If Reduction: replaie");
        }

        return this.reduce(ho);
    }

    public static boolean applyTo(Modules modules,HaskellProof hp,Abortion aborter){
        IfReduction lr = new IfReduction();
        lr.setHaskellProof(hp);
        lr.prelude = modules.getPrelude();
        lr.trueEntity  = lr.checkNull(lr.getEntity("True"));
        lr.falseEntity = lr.checkNull(lr.getEntity("False"));
        if (lr.nullCheck) {
            return false;
        }
        lr.forModules(modules);
        return lr.wasChanged();
        //return true;
    }
}
