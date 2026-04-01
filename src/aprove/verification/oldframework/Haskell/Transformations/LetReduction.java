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
import aprove.verification.oldframework.Haskell.Visitors.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 */
public class LetReduction extends BasicReduction {
     Map<Deepcopy,Deepcopy> copyMap;

     List<HaskellEntity> moduleCollects = new LinkedList<HaskellEntity>();

     void adaptFunction(List<Var> freeVars,List<String> names, VarEntity funcEntity,Map<VarEntity,List<HaskellObject>> repAppMap){

        // function symbol with new Name
        Function func = (Function) funcEntity.getValue();
        func.setSymbol(new HaskellNamedSym(funcEntity));

        // new ruleType
        HaskellType ruleType = func.getTypeTerm();
        List<HaskellType> hts = HaskellTools.getTypeTerms(freeVars);
        ruleType = (HaskellType) this.prelude.buildArrows(hts,ruleType);
        TypeSchema ts = (TypeSchema) funcEntity.getType();
        Set<ClassConstraint> ccs = this.getCurrentConstraints(ruleType);
        if (ts != null) {
            ts.setMatrix(this.prelude.buildArrows(Copy.deepCol(hts),ts.getMatrix()));
            ts.getConstraints().addAll(ccs);
        }
        ts = this.getCurModules().getAssumptions().getTypeSchemaFor(funcEntity);
        ts.setMatrix(this.prelude.buildArrows(Copy.deepCol(hts),ts.getMatrix()));
        ts.getConstraints().addAll(ccs);
        // extend the patterns of each rule
        for(HaskellRule rule : func.getRules()){
            List<HaskellPat> pats = new Vector<HaskellPat>();
            EntityFrame eframe = rule.getEntityFrame();
            eframe.setParentEntityFrame(funcEntity.getModule());
            Map<HaskellEntity,HaskellObject> mapE2V = new HashMap<HaskellEntity,HaskellObject>();
            Iterator<String> nit = names.iterator();
            for(Var var : freeVars){
                 HaskellEntity entity = var.getSymbol().getEntity();
                 HaskellEntity newEntity = new VarEntity(nit.next(),this.curModule,null,null,true);
                 eframe.addEntity(newEntity);
                 Var newVar = new Var(new HaskellNamedSym(newEntity));
                 newVar.setTypeTerm(var.getTypeTerm());
                 mapE2V.put(entity,newVar);
                 pats.add(newVar);
            }
            VarEntityApplyAddVisitor veaav = new VarEntityApplyAddVisitor(this.prelude,repAppMap);
            rule.visit(veaav);
            rule.visit(new VarEntitySubstitutor(mapE2V));
            rule.getPatterns().addAll(0,pats);
            rule.setTypeTerm(ruleType);
        }
        func.setTypeTerm(ruleType);

    }

    void addNeededRenames(Map<VarEntity,HaskellObject> repMap,LetExp ho,Set<String> needRename){
        Set<Var> boundedVars = new HashSet<Var>();
        ho.getExpression().visit(new BoundedLocalVarCollector(boundedVars));
        for (Var var : boundedVars){
            VarEntity e = (VarEntity) var.getSymbol().getEntity();
            if (needRename.contains(e.getName())) {
                e.setName(this.prelude.getNextNameFor(e.getName()));
                repMap.put(e,new Var(new HaskellNamedSym(e)).setTypeTerm(var.getTypeTerm()));
            }
        }
    }

    private String firstUp(String name){
        StringBuffer nbuf = new StringBuffer(name);
        nbuf.setCharAt(0,Character.toUpperCase(name.charAt(0)));
        return nbuf.toString();
    }

    private String firstLow(String name){
        StringBuffer nbuf = new StringBuffer(name);
        nbuf.setCharAt(0,Character.toLowerCase(name.charAt(0)));
        return nbuf.toString();
    }

    @Override
    public void fcaseLetExp(LetExp ho){
        LetExp old = (LetExp) this.copyMap.get(ho);
        Module oldModule = (Module) this.copyMap.get(this.getCurModule());
        Set<HaskellObject> neededSet = new LinkedHashSet<HaskellObject>();
        super.fcaseLetExp(ho);
        String namePrefix = "";
        for (Function func : this.functions){
            namePrefix = namePrefix + this.firstUp(this.prelude.correctName(func.getSymbol().getEntity().getName()));
        }
        namePrefix = this.firstLow(namePrefix);
        EntityFrame eframe = ho.getEntityFrame();
        Map<VarEntity,List<HaskellObject>> repAppMap = new HashMap<VarEntity,List<HaskellObject>>();
        Map<VarEntity,HaskellObject> repMap = new HashMap<VarEntity,HaskellObject>();
        Set<String> needRename = new HashSet<String>();


        // collect freeEntities
        List<Var> freeVars = new Vector<Var>();
        FreeLocalVarCollector flvc = new FreeLocalVarCollector(freeVars);
        for (HaskellEntity e : eframe.getCollectedEntities()){
                if (e instanceof VarEntity) {
                    e.visit(flvc);
                }
        }

        // transfer only free VarEntities to a list
        List<VarEntity> freeVarEntities = new Vector<VarEntity>();
        List<String> names = new Vector<String>();
        for(Var var : freeVars){
            needRename.add(var.getSymbol().getEntity().getName());
            names.add(this.getNextNewNameForVariable());
        }

        for (HaskellEntity e : eframe.getCollectedEntities()){
            List<HaskellObject> rep = new Vector<HaskellObject>();
        // new unique Name
            VarEntity funcEntity = (VarEntity) e;
            String newName = namePrefix+this.firstUp(this.prelude.correctName(funcEntity.getName()));

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println(" LetReduction new Function: "+newName+" "+this.curModule);
            }

            newName = this.prelude.getFreshNameFor(newName);
            funcEntity.setName(newName);
            rep.add(new HaskellNamedSym(funcEntity));
            rep.addAll(Copy.deepCol(freeVars));
            repAppMap.put(funcEntity,rep);
        }

        for (HaskellEntity e : eframe.getCollectedEntities()){
            if (e instanceof VarEntity) {
                this.adaptFunction(freeVars,names,(VarEntity)e,repAppMap);
                this.moduleCollects.add(e);
                neededSet.add(e);
            }
        }

        this.addNeededRenames(repMap,ho,needRename);
        VarEntitySubstitutor ves = new VarEntitySubstitutor(repMap);
        for (HaskellEntity e : eframe.getCollectedEntities()){
            if (e instanceof VarEntity) {
                e.visit(ves);
            }
        }

        VarEntityApplyAddVisitor veaav = new VarEntityApplyAddVisitor(this.prelude,repAppMap);
        ho.setExpression((HaskellExp) ho.getExpression().visit(veaav).visit(ves));

        this.setChanged();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("Let Reduction: replace");
        }

        this.proofAdd(old,oldModule,neededSet,this.getCurModule());
    }

    @Override
    public HaskellObject caseLetExp(LetExp ho){
        ho = (LetExp) super.caseLetExp(ho);
        return ho.getExpression();
    }

    @Override
    public Module caseModule(Module ho){
        while (!this.moduleCollects.isEmpty()){
             HaskellEntity e = this.moduleCollects.remove(0);
             ho.addEntity(e);
             e.visit(this);  // possible new entities added to moduleCollects
        }
        ho = (Module) super.caseModule(ho);
        return ho;
    }

    public static boolean applyTo(Modules modules,HaskellProof hp,Map copyMap,Abortion aborter){
        LetReduction lr = new LetReduction();
        lr.setAborter(aborter);
        lr.copyMap = copyMap;
        lr.setHaskellProof(hp);
        lr.forModules(modules);
        return lr.wasChanged();
        //return true;
    }

    @Override
    public boolean guardLetFrame(LetExp ho)            { return false;}

}
