package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.HaskellProblem.Processors.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
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
 * The CondReduction reduces condition stacks in a function definition
 * to new functions
 * Example:
 *  f x | x == 1 = 5   <br/>
 *  f _ = 0            <br/>
 * is expanded to      <br/>
 *  f x = u x (x == 1) <br/>
 *  u x True = 5       <br/>
 *  u x False = 0      <br/>
 */
public class CondReduction extends BasicReduction {

    Map<Deepcopy,Deepcopy> copyMap;

    HaskellEntity equal;
    HaskellEntity minus;
    HaskellEntity and;
    HaskellEntity geq;

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

    private HaskellEntity getEntityVar(String name){
        return this.prelude.getEntityN(this,"Prelude",name,HaskellEntity.Sort.VAR);
    }

    private HaskellObject buildTerm(HaskellEntity entity,HaskellType res,HaskellObject par1,HaskellObject par2){
        Var var = new Var(new HaskellNamedSym(entity));
        var.setTypeTerm(this.prelude.buildArrow(par1.getTypeTerm(),this.prelude.buildArrow(par2.getTypeTerm(),res)));
        return this.prelude.buildApply(this.prelude.buildApply(var,par1),par2);
    }

    private HaskellObject buildNumCondition(HaskellPat hp,Var var,Map<HaskellEntity,HaskellObject> mapE2V) {
         if (hp == null){
            return this.buildCons(this.trueEntity);
         } else if (hp instanceof PlusPat){
            PlusPat pp = (PlusPat) hp;
            IntegerLit il = pp.getInteger(); // k
            HaskellObject n_minus_k = this.buildTerm(this.minus,var.getTypeTerm(),Copy.deep(var),Copy.deep(il));
            mapE2V.put(pp.getVariable().getSymbol().getEntity(),n_minus_k);
            return this.buildTerm(this.geq,new Cons(this.prelude.getBoolSym()),var,il);
         } else {
            return this.buildTerm(this.equal,new Cons(this.prelude.getBoolSym()),var,hp);
         }
    }

    private HaskellExp buildFunction(String newName,List<Var> freeVars,CondExp ce,HaskellExp next,Set<VarEntity> curNeeded,EntityFrame curEntityFrame) {
        HaskellExp cond  = ce.getCondition();
        if (cond instanceof Cons){
            HaskellEntity e = ((Cons)cond).getSymbol().getEntity();
            if (e == this.trueEntity){
                curNeeded.clear();
                return ce.getResult();
            }
            if (e == this.falseEntity){
                // If there is no next term, then build a function expecting True
                // but being called with this False
                if (next != null) {
                    return next;
                }
            }
        }
        Module curModule = this.getCurModule();

        VarEntity newVarEntity = new VarEntity(newName,curModule,null,null);
        List<HaskellRule> newRules = new Vector<HaskellRule>();

        List<HaskellType> hts = HaskellTools.getTypeTerms(freeVars);
        hts.add(ce.getCondition().getTypeTerm());
        hts.add(ce.getResult().getTypeTerm());

        HaskellType ruleType = this.prelude.buildArrows(hts);

        HaskellExp repTerm = new Var(new HaskellNamedSym(newVarEntity));
        repTerm.setTypeTerm(ruleType);
        repTerm =(HaskellExp) this.prelude.buildApplies(repTerm,Copy.deepCol(freeVars));
        repTerm =(HaskellExp) this.prelude.buildApply(repTerm,Copy.deep(ce.getCondition()));

        // new EntityFrame and Entity Replacemap

        HaskellPat hTrue = this.buildCons(this.trueEntity);
        HaskellPat hFalse = this.buildCons(this.falseEntity);
        HaskellPat[] curPat = new HaskellPat[]{hTrue,hFalse};
        HaskellExp[] curRes = null;
        if (next == null) {
            curRes = new HaskellExp[]{ce.getResult()};
        } else {
            curRes = new HaskellExp[]{ce.getResult(),next};
        }

        for(int i=0;i<curRes.length;i++){
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
            pats.add(curPat[i]);
            HaskellExp res = Copy.deep(curRes[i]);
            res = (HaskellExp)res.visit(new VarEntitySubstitutor(mapE2V));
            eframe.setParentEntityFrame(curEntityFrame);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println();
            }

            HaskellRule newRule = new HaskellRule(eframe,pats,res);
            newRule.setTypeTerm(ruleType);
            newRules.add(newRule);
        }

        Function newFunction = new Function(new HaskellNamedSym(newVarEntity),newRules);
        newFunction.setTypeTerm(ruleType);
        newVarEntity.setValue(newFunction);
        curNeeded.add(newVarEntity);
        return repTerm;
    }


    public VarEntity buildPatCheckFunction(VarEntity lastFunc,List<HaskellObject> nextPats,HaskellType condRuleType,VarEntity nextFunc,HaskellType ruleType,HaskellExp condStart,boolean last){
        VarEntity newVarEntity = new VarEntity(this.getNextNewNameFromFunction(),this.curModule,null,null);

        Module curModule = this.getCurModule();
        EntityFrame curEntityFrame = this.getCurEntityFrame();

        List<HaskellRule> newRules = new Vector<HaskellRule>();

        List<Var> freeVars = new Vector<Var>();
        FreeLocalVarCollector flvc = new FreeLocalVarCollector(freeVars);
        for (HaskellObject obj : nextPats){
           obj.visit(flvc);
        }

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

        List<HaskellPat> pats = new Vector<HaskellPat>();
        HaskellExp res = null;
        if (lastFunc == null) {
            res = condStart;
            if(condStart instanceof LetExp) {
                ((LetExp) condStart).getEntityFrame().setParentEntityFrame(eframe);
            }
        } else {
           res = new Var(new HaskellNamedSym(lastFunc));
           res.setTypeTerm(condRuleType);
        }
        boolean first = true;
        for (HaskellObject obj : nextPats){
            if (lastFunc != null) {
                res = (HaskellExp) this.prelude.buildApply(res,Copy.deep(obj));
            }
            if (!(last && first)) {
                if (first) {
                    pats.add(this.buildCons(this.trueEntity));
                } else {
                    pats.add((HaskellPat)obj);
                }
            }
            first = false;
        }
        eframe.setParentEntityFrame(curEntityFrame);
        HaskellRule newRule = new HaskellRule(eframe,pats,res);
        newRule.visit(new VarEntitySubstitutor(mapE2V));
        newRule.setTypeTerm(last ? ruleType : condRuleType);
        newRules.add(newRule);

        if (nextFunc != null){
            EntityFrame eframe2 = new EntityFrame.EntityFrameSkeleton(curEntityFrame,new EntityMap());
            List<HaskellPat> pats2 = new Vector<HaskellPat>();
            HaskellExp res2 = new Var(new HaskellNamedSym(nextFunc));
            res2.setTypeTerm(ruleType);
            first = true;
            for (HaskellObject obj : nextPats){
                if (!(last && first)) {
                    String name = this.getNextNewNameForVariable();
                    HaskellEntity newEntity = new VarEntity(name,curModule,null,null,true);
                    eframe2.addEntity(newEntity);
                    Var var = new Var(new HaskellNamedSym(newEntity));
                    var.setTypeTerm(obj.getTypeTerm());
                    pats2.add(var);
                    if (!first) {
                        res2 = (HaskellExp) this.prelude.buildApply(res2,Copy.deep(var));
                    }
                }
                first = false;
            }
            eframe2.setParentEntityFrame(curEntityFrame);
            HaskellRule newRule2 = new HaskellRule(eframe2,pats2,res2);
            newRule2.setTypeTerm(last ? ruleType : condRuleType);
            newRules.add(newRule2);
        }

        Function newFunction = new Function(new HaskellNamedSym(newVarEntity),newRules);
        newFunction.setTypeTerm(last ? ruleType : condRuleType);
        newVarEntity.setValue(newFunction);
        this.createAssumptionFor(newFunction);
        this.addToEntityFrame(newVarEntity);
        return newVarEntity;
    }

    public HaskellExp buildLastCall(VarEntity ve,List<HaskellPat> pats,HaskellType resType){
         List<HaskellType> hts = HaskellTools.getTypeTerms(pats);
         hts.add(resType);
         HaskellType ruleType = this.prelude.buildArrows(hts);
         HaskellExp repTerm = new Var(new HaskellNamedSym(ve));
         repTerm.setTypeTerm(ruleType);
         repTerm =(HaskellExp) this.prelude.buildApplies(repTerm,Copy.deepCol(pats));
         return repTerm;
    }

    public VarEntity buildForRule(HaskellRule ho,VarEntity nextFunc,Set<HaskellObject> neededSet){
        LetExp whereExp = null;
        HaskellExp exp = ho.getExpression();
        CondStackExp cte = null;
        if (exp instanceof LetExp){
            // if a where-clause occurs the real cond stack is there in encapsulated
            whereExp = (LetExp) exp;
            HaskellExp cexp = whereExp.getExpression(); // get the cond stack
            if (cexp instanceof CondStackExp){  // if it is a cond stack:
                cte = (CondStackExp) cexp;
            } else {
               whereExp = null; // only if a condstack with where occur the whereExp needs a special handling
            }
        } else if (exp instanceof CondStackExp) {
            cte = (CondStackExp) exp;
        }

        //----------
        List<HaskellPat> pats = ho.getPatterns();

        List<HaskellType> hts = HaskellTools.getTypeTerms(pats);
        hts.add(exp.getTypeTerm());
        HaskellType ruleType = this.prelude.buildArrows(hts);
        hts.add(0,new Cons(this.prelude.getBoolSym()));
        HaskellType condRuleType = this.prelude.buildArrows(hts);

        Map<HaskellEntity,HaskellObject> mapE2V = new HashMap<HaskellEntity,HaskellObject>();
        List<List<HaskellObject>> patStack = new Vector<List<HaskellObject>>();
        List<HaskellEntity> currentEntities = new Vector<HaskellEntity>();
        List<HaskellObject> nPats = null;
        HaskellPat nsvpat = null;
        boolean start = true;
        List<HaskellObject> nextPats = null;
        do {
            NumSplitVisitor nsv = new NumSplitVisitor(this.curModule,currentEntities,this.prelude);
            pats = nsv.applyTo(pats);
            nsvpat = nsv.getNumPattern();
            Var nsvvar = nsv.getVariable();
            HaskellObject cond = this.buildNumCondition(nsvpat,nsvvar,mapE2V);
            nextPats = nsv.getCopies();
            if (nsvvar != null) {
                currentEntities.remove(nsvvar.getSymbol().getEntity());
            }
            if (start) {
                nPats = Copy.deepCol(nextPats);
            }
            start = false;
            nextPats.add(0,cond);
            patStack.add(0,nextPats);
        } while (nsvpat != null);

        // ----
        // collect the free vars in the patterns of current rule and add them to the var-context
        List<Var> freeVars = new Vector<Var>();
        FreeLocalVarCollector flvc = new FreeLocalVarCollector(freeVars);
        for (HaskellObject obj : nextPats){
           obj.visit(flvc);
        }

        exp = (HaskellExp) exp.visit(new VarEntitySubstitutor(mapE2V));
        HaskellExp next = null;
        if (cte != null){
            // yes it is cond stack so build all the condition check functions
            next = nextFunc == null ? null : this.buildLastCall(nextFunc,ho.getPatterns(),exp.getTypeTerm());
            EntityFrame fEntityFrame =  whereExp != null ? whereExp.getEntityFrame() : this.getCurEntityFrame();
            ListIterator<CondExp> it = cte.getConditions().listIterator(cte.getConditions().size());
            Set<VarEntity> curNeeded = new HashSet<VarEntity>();
            while(it.hasPrevious()){
                next = this.buildFunction(this.getNextNewNameFromFunction(),freeVars,it.previous(),next,curNeeded,fEntityFrame);
            }
            for (VarEntity nve : curNeeded){
                this.createAssumptionFor((Function)nve.getValue());
                if (whereExp != null) {
                   whereExp.getEntityFrame().addEntity(nve);
                }  else {
                   this.addToEntityFrame(nve);
                   neededSet.add(nve);
                }
            }
            if (whereExp != null) { // put the where frame around
                whereExp.setExpression(next);
                next = whereExp;
            }
        } else {
            // no it is no cond stack, so directly the old expression (with let encapsulation) is used
            next = exp;
        }

        // now the the pattern check head calls the "next" expression (cond stack emulation or the old expression)
        Iterator<List<HaskellObject>> it = patStack.iterator();
        boolean last = false;
        nextPats = null;
        VarEntity lastFunc = null;
        do {
             nextPats = it.next();
             last = !it.hasNext();
             lastFunc = this.buildPatCheckFunction(lastFunc,nextPats,condRuleType,nextFunc,ruleType,next,last);
             neededSet.add(lastFunc);
        } while (!last);

        // old rule modification: new Patterns, new call of sub functions
        List<Var> vars = new Vector<Var>();
        flvc = new FreeLocalVarCollector(vars);
        List<HaskellPat> hpats = new Vector<HaskellPat>();
        for (HaskellObject obj : nPats){
            hpats.add((HaskellPat) obj);
            obj.visit(flvc);
        }
        ho.setPatterns(hpats);
        ho.getEntityFrame().setCollectedEntities(new EntityMap());
        for (Var var : vars){
            ho.getEntityFrame().addEntity(var.getSymbol().getEntity());
        }

        HaskellExp repTerm = new Var(new HaskellNamedSym(lastFunc));
        repTerm.setTypeTerm(ruleType);
        repTerm =(HaskellExp) this.prelude.buildApplies(repTerm,Copy.deepCol(hpats));
        ho.setExpression(repTerm);

        this.setChanged();
        return lastFunc;
    }

    @Override
    public HaskellObject caseFunction(Function ho){
        boolean need = false;
        for (HaskellRule rule : ho.getRules()){
            if (NumOccurVisitor.applyTo(rule.getPatterns())) {
                need = true; break;
            }
            HaskellExp exp = rule.getExpression();
            if (exp instanceof LetExp) {
                exp = ((LetExp) exp).getExpression();
            }
            if (exp instanceof CondStackExp) {
                need = true; break;
            }
        }
        if (need) {
            HaskellObject old = (HaskellObject) this.copyMap.get(ho);
            Module oldModule = (Module) this.copyMap.get(this.getCurModule());
            Set<HaskellObject> neededSet = new LinkedHashSet<HaskellObject>();
            neededSet.add(ho);
            ListIterator<HaskellRule> lit = ho.getRules().listIterator(ho.getRules().size());
            VarEntity e = null;
            while (lit.hasPrevious()){
                e = this.buildForRule(lit.previous(),e,neededSet);
            }
            this.proofAdd(old,oldModule,(Object)neededSet,this.getCurModule());
        }
        ho = (Function) super.caseFunction(ho);
        return ho;
    }

    public static boolean applyTo(Modules modules,HaskellProof hp,Map copyMap,Abortion aborter){
        CondReduction lr = new CondReduction();
        lr.setAborter(aborter);
        lr.copyMap = copyMap;
        lr.setHaskellProof(hp);
        lr.prelude = modules.getPrelude();
        lr.trueEntity  = lr.checkNull(lr.getEntity("True"));
        lr.falseEntity = lr.checkNull(lr.getEntity("False"));
        lr.equal = lr.checkNull(lr.getEntityVar("=="));
        lr.minus = lr.checkNull(lr.getEntityVar("-"));
        lr.and   = lr.checkNull(lr.getEntityVar("&&"));
        lr.geq   = lr.checkNull(lr.getEntityVar(">="));
        //if (lr.nullCheck) return false;
        lr.forModules(modules);
        return lr.wasChanged();
        //return true;
    }
}
