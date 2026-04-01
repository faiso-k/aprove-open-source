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
 */
public class LambdaReduction extends BasicReduction {

    private HaskellExp reduce(LambdaExp le) {
         Module curModule = this.getCurModule();
         EntityFrame curEntityFrame = this.getCurEntityFrame();
         String newName = this.getNextNewNameFromFunction();
         List<Var> freeVars = new Vector<Var>();
         le.visit(new FreeLocalVarCollector(freeVars));

         List<HaskellPat> pats = new Vector<HaskellPat>();
         EntityFrame eframe = le.getEntityFrame();

         Map<HaskellEntity,HaskellObject> mapE2V = new HashMap<HaskellEntity,HaskellObject>();
         VarEntity newVarEntity = new VarEntity(newName,curModule,null,null);

         le.getPatterns();
         for(Var var : freeVars){
             HaskellEntity entity = var.getSymbol().getEntity();
             HaskellEntity newEntity = new VarEntity(entity.getName(),curModule,null,null,true);
             eframe.addEntity(newEntity);
             Var newVar = new Var(new HaskellNamedSym(newEntity));
             newVar.setTypeTerm(var.getTypeTerm());
             mapE2V.put(entity,newVar);
             pats.add(newVar);
         }
         HaskellExp res = le.getResult();
         res = (HaskellExp) res.visit(new VarEntitySubstitutor(mapE2V));
         pats.addAll(le.getPatterns());

         HaskellExp repTerm = new Var(new HaskellNamedSym(newVarEntity));
         List<HaskellType> hts = HaskellTools.getTypeTerms(pats);
         hts.add(res.getTypeTerm());
         HaskellType ruleType = this.prelude.buildArrows(hts);
         repTerm.setTypeTerm(ruleType);
         repTerm =(HaskellExp) this.prelude.buildApplies(repTerm,Copy.deepCol(freeVars));

         eframe.setParentEntityFrame(curEntityFrame);
         HaskellRule newRule = new HaskellRule(eframe,pats,res);
         newRule.setTypeTerm(ruleType);
         List<HaskellRule> newRules = new Vector<HaskellRule>();
         newRules.add(newRule);
         Function newFunction = new Function(new HaskellNamedSym(newVarEntity),newRules);
         newFunction.setTypeTerm(ruleType);
         newVarEntity.setValue(newFunction);
         this.createAssumptionFor(newFunction);
         this.addToEntityFrame(newVarEntity);
         this.proofAdd(le,curModule,newVarEntity,curModule);
         return repTerm;
    }

    @Override
    public HaskellObject caseLambdaExp(LambdaExp ho) {
        this.setChanged();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("Lambda Reduction: replace");
        }

        return this.reduce(ho);
    }

    public static boolean applyTo(Modules modules,HaskellProof hp,Abortion aborter){
        LambdaReduction lr = new LambdaReduction();
        lr.setHaskellProof(hp);
        lr.forModules(modules);
        return lr.wasChanged();
        //return true;
    }
}
