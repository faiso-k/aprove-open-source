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
 * CaseReduction reduces the case structure of Haskell to a new function
 * and adds a call of this function.
 */
public class CaseReduction extends BasicReduction {

    private HaskellExp reduce(CaseExp ce) {
         Module curModule = this.getCurModule();
         EntityFrame curEntityFrame = this.getCurEntityFrame();
         String newName = this.getNextNewNameFromFunction();
         List<Var> freeVars = new Vector<Var>();
         ce.listWalk(ce.getCases(),new FreeLocalVarCollector(freeVars));

         VarEntity newVarEntity = new VarEntity(newName,curModule,null,null);
         List<HaskellRule> newRules = new Vector<HaskellRule>();
         List<HaskellType> hts = HaskellTools.getTypeTerms(freeVars);
         hts.add(ce.getArgument().getTypeTerm());
         hts.add(ce.getTypeTerm());

         HaskellType ruleType = this.prelude.buildArrows(hts);

         HaskellExp repTerm = new Var(new HaskellNamedSym(newVarEntity));
         repTerm.setTypeTerm(ruleType);
         repTerm =(HaskellExp) this.prelude.buildApplies(repTerm,Copy.deepCol(freeVars));
         repTerm =(HaskellExp) this.prelude.buildApply(repTerm,ce.getArgument());

         for(AltExp ae : ce.getCases()){
            List<HaskellPat> pats = new Vector<HaskellPat>();
            EntityFrame eframe = ae.getEntityFrame();
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
            HaskellExp res = ae.getExpression();
            res = (HaskellExp)res.visit(new VarEntitySubstitutor(mapE2V));
            pats.add(ae.getPattern());
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
         this.proofAdd(ce,curModule,newVarEntity,curModule);
         return repTerm;
    }

    @Override
    public HaskellObject caseCaseExp(CaseExp ho) {
        this.setChanged();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("Case Reduction: replace");
        }

        return this.reduce(ho);
    }

    public static boolean applyTo(Modules modules,HaskellProof hp,Abortion aborter){
        CaseReduction lr = new CaseReduction();
        lr.setAborter(aborter);
        lr.setHaskellProof(hp);
        lr.forModules(modules);
        return lr.wasChanged();
        //return true;
    }
}
