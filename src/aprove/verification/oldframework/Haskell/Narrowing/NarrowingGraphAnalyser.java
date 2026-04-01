package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public abstract class NarrowingGraphAnalyser {

    public static final int DPsReplacer = 0;

    public static final int RulesReplacer = 1;

    int count;

    HaskellEntity errorEntity;

    String graph;

    Module module;

    Modules modules;

    Prelude prelude;

    HaskellEntity terminatorEntity;

    private NarrowNode freeAppNode;

    public NarrowingGraphAnalyser(Modules modules, NarrowNode freeAppNode) {
        this.modules = modules;
        this.prelude = this.modules.getPrelude();
        this.errorEntity = this.getEntity("error", HaskellEntity.Sort.VAR);
        this.terminatorEntity = this.getEntity("terminator", HaskellEntity.Sort.VAR);
        this.module = this.modules.getMainModule();
        this.graph = "";
        this.freeAppNode = freeAppNode;
    }

    public void addVar(
        List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> target,
        HaskellSubstitution tySubs,
        HaskellSubstitution subs,
        NarrowNode node
    ) {
        target.add(
            new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(
                tySubs,
                subs,
                (HaskellExp)new Var(new HaskellNamedSym(this.getFreshVar())).setTypeTerm(
                    Copy.deep(node.getExpression().getTypeTerm())
                )
            )
        );
    }

    public HaskellExp buildReplaceFor(int pos, NarrowNode node) {
        if (node.getTag() == null) {
            node.setTag(new Tag());
        }
        HaskellExp rep = ((Tag)node.getTag()).getRep(pos);
        if (rep == null) {
            HaskellExp exp = node.getExpression();
            List<Var> freeVars = new Vector<Var>();
            FreeLocalVarCollector flvc = new FreeLocalVarCollector(freeVars);
            exp.visit(flvc);
            List<HaskellType> hts = HaskellTools.getTypeTerms(freeVars);
            Set<HaskellSym> freeTypeVarSyms = new LinkedHashSet<HaskellSym>();
            (new TypeAnnotationVarSymCollector(freeTypeVarSyms)).applyTo(exp);
            for (HaskellSym freeTypeVarSym : freeTypeVarSyms) {
                hts.add(this.prelude.getKindStar());
                Var typeVar = new Var(freeTypeVarSym);
                typeVar.setTypeTerm(this.prelude.getKindStar());
                freeVars.add(typeVar);
            }
            hts.add(exp.getTypeTerm());
            Var repVar = new Var(new HaskellNamedSym(this.getFreshFunction(exp)));
            repVar.setTypeTerm(this.prelude.buildArrows(hts));
            ((Tag)node.getTag()).setRep(pos, ((HaskellExp)this.prelude.buildApplies(repVar, freeVars)));
        }
        return ((Tag)node.getTag()).getRep(pos);
    }

    public void buildTerms(
        HaskellSubstitution tySubs,
        HaskellSubstitution subs,
        NarrowNode node,
        List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> target,
        boolean head,
        int replacer,
        boolean para,
        List<NarrowNode> rheads
    ) {
        boolean varExpPredOrFreeAppPred = this.isVarExpFreeAppPred(node);
        if (node.isRoot()) {
            if (!head) {
                if (para && varExpPredOrFreeAppPred) {
                    this.addVar(target, tySubs, subs, node);
                    return;
                }
                HaskellExp baseReplace = this.buildReplaceFor(replacer, node);
                target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, baseReplace));
                return;
            }
        }
        switch (node.getMode()) {
            case NON:
                if (para && varExpPredOrFreeAppPred) {
                    this.addVar(target, tySubs, subs, node);
                    return;
                }
                if (node.getChildren() != null) {
                    for (NarrowNode child : node.getChildren()) {
                        this.buildTerms(tySubs, subs, child, target, false, replacer, para, rheads);
                    }
                }
                return;
            case CASE: {
                if (para) {
                    if (varExpPredOrFreeAppPred) {
                        this.addVar(target, tySubs, subs, node);
                        return;
                    }
                    HaskellExp baseReplace = this.buildReplaceFor(replacer, node);
                    target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, baseReplace));
                    rheads.add(node);
                    return;
                }
                Iterator<HaskellSubstitution> it = ((CaseAnnotation)node.getAnnotation()).getSubstitutions().iterator();
                for (NarrowNode child : node.getChildren()) {
                    this.buildTerms(tySubs, subs.combineWith(it.next()), child, target, false, replacer, para, rheads);
                }
                return;
            }
            case TYCASE: {
                if (para) {
                    if (varExpPredOrFreeAppPred) {
                        this.addVar(target, tySubs, subs, node);
                        return;
                    }
                    HaskellExp baseReplace = this.buildReplaceFor(replacer, node);
                    target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, baseReplace));
                    rheads.add(node);
                    return;
                }
                Iterator<HaskellSubstitution> it = ((TyCaseAnnotation)node.getAnnotation()).getTySubstitutions().iterator();
                for (NarrowNode child : node.getChildren()) {
                    this.buildTerms(tySubs.combineWith(it.next()), subs, child, target, false, replacer, para, rheads);
                }
                return;
            }
            case VAREXP: {
                /*List<Triple<Substitution,Substitution,HaskellExp>> pbs = new Vector<Triple<Substitution,Substitution,HaskellExp>>();
                NarrowNode baseNarrowNode = node.getChildren().iterator().next();
                this.buildTerms(tySubs,subs,baseNarrowNode,pbs,false,replacer,rheads);
                for (Triple<Substitution,Substitution,HaskellExp> sse : pbs){
                    sse.z = (HaskellExp)(((Apply) (sse.z)).getFunction());
                    target.add(sse);
                } */
                //this.addVar(target,tySubs,subs,node);
                // TODO verify
                HaskellExp baseReplace = this.buildReplaceFor(replacer, node);
                target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, baseReplace));
                return;
            }
            case CONS: {
                ConsAnnotation ca = (ConsAnnotation)node.getAnnotation();
                HaskellObject cBase = ca.getCBase();
                List<Var> vars = ca.getVars();
                List<NarrowNode> children = node.getChildren();
                Collection[] cross = new Collection[children.size()];
                InstanceCombinator aCombi =
                    new InstanceCombinator((HaskellExp)cBase, vars, tySubs, subs, new HaskellSubstitution());
                int i = 0;
                for (NarrowNode child : children) {
                    List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> pbs =
                        new Vector<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>>();
                    this.buildTerms(tySubs, subs, child, pbs, false, replacer, true, rheads);
                    cross[i] = pbs;
                    i++;
                }
                Collection_Util.crossProduct(cross, aCombi, target);
                return;
            }
            case INSTANCE: {
                if (para && varExpPredOrFreeAppPred) {
                    this.addVar(target, tySubs, subs, node);
                    return;
                }
                InstanceAnnotation instanceAnnotation = (InstanceAnnotation)node.getAnnotation();
                NarrowNode baseNarrowNode = instanceAnnotation.getBase();
                HaskellSubstitution tyMatchSub = instanceAnnotation.getTyMatchSubs();
                List<Var> vars = instanceAnnotation.getVars();
                HaskellExp baseReplace = this.buildReplaceFor(replacer, baseNarrowNode);
                List<NarrowNode> children = node.getChildren();
                Collection[] cross = new Collection[children.size()];
                InstanceCombinator iCombi = new InstanceCombinator(baseReplace, vars, tySubs, subs, tyMatchSub);
                int i = 0;
                replacer = NarrowingGraphAnalyser.RulesReplacer;
                //HaskellSym.showee(node);
                for (NarrowNode child : children) {
                    List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> pbs =
                        new Vector<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>>();
                    this.buildTerms(tySubs, subs, child, pbs, false, replacer, true, rheads);
                    cross[i] = pbs;
                    i++;
                }
                Collection_Util.crossProduct(cross, iCombi, target);
                return;
            }
            case PROGERROR:
                target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, node.getExpression()));
                return;
            case UNIVAR: {
                if (para && varExpPredOrFreeAppPred) {
                    this.addVar(target, tySubs, subs, node);
                    return;
                }
                Var var = ((UniVarAnnotation)node.getAnnotation()).getVar();
                List<NarrowNode> children = node.getChildren();
                Collection[] cross = new Collection[children.size()];
                ArgumentCombinator aCombi = new ArgumentCombinator(var, tySubs, subs, this);
                int i = 0;
                for (NarrowNode child : children) {
                    List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> pbs =
                        new Vector<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>>();
                    this.buildTerms(tySubs, subs, child, pbs, false, replacer, true, rheads);
                    cross[i] = pbs;
                    i++;
                }
                Collection_Util.crossProduct(cross, aCombi, target);
                return;
            }
            case FIRST:
            default:
                //                throw new RuntimeException("incorrect node annotation");
        }
    }

    public VarEntity getFreshFunction(HaskellExp exp) {
        exp = (HaskellExp)HaskellTools.applyFlatten(exp).get(0);
        VarEntity ve = (VarEntity)((Var)exp).getSymbol().getEntity();
        String name = ve.getName();
        name = this.prelude.correctName(name);
        return new VarEntity(this.prelude.getFreshNameFor("new_" + name), ve.getModule(), null, null, false);
    }

    public VarEntity getFreshVar() {
        String name = "xx" + this.count;
        this.count++;
        return new VarEntity(this.prelude.getFreshNameFor(name), this.module, null, null, true);
    }

    public String getGraph() {
        return this.graph;
    }

    public boolean isVarExpFreeAppPred(NarrowNode node) {
        Tag tag = (Tag)node.getTag();
        if (tag == null) {
            return false;
        }
        return tag.getVarExpFreeAppPred();
    }

    public boolean markVarExpFreeAppPreds(NarrowNode node) {
        if (node.getMark() != this) {
            if (node.getTag() == null) {
                node.setTag(new Tag());
            }
            node.setMark(this);
            boolean isChild = false;
            switch (node.getMode()) {
                case UNIVAR:
                    if (node.getChildren() != null) {
                        isChild = !node.getChildren().isEmpty();
                        for (NarrowNode child : node.getChildren()) {
                            isChild = this.markVarExpFreeAppPreds(child) || isChild;
                        }
                    }
                    return ((Tag)node.getTag()).setVarExpFreeAppPred(isChild);
                case NON: {
                    // checking for terminator entity
                    HaskellObject exp =
                        HaskellTools.getSubtermByID((BasicTerm)node.getExpression(), node.getEvalSubtermID());
                    HaskellObject head = HaskellTools.getLeftMost(exp);
                    if (head instanceof Var) {
                        Var v = (Var)head;
                        VarEntity ve = (VarEntity)v.getSymbol().getEntity();
                        if (ve == this.terminatorEntity) {
                            // a predecessor of a terminator is also like a UNIVAR, since it introduces a fresh variable
                            isChild = true;
                        }
                    }
                    // process the children of this node further
                    if (node.getChildren() != null) {
                        for (NarrowNode child : node.getChildren()) {
                            isChild = this.markVarExpFreeAppPreds(child) || isChild;
                        }
                    }
                    return ((Tag)node.getTag()).setVarExpFreeAppPred(isChild);
                }
                case CASE:
                case TYCASE:
                    //case UNIVAR:
                case CONS: {
                    isChild = (node == this.freeAppNode);
                    if (node.getChildren() != null) {
                        for (NarrowNode child : node.getChildren()) {
                            isChild = this.markVarExpFreeAppPreds(child) || isChild;
                        }
                    }
                    return ((Tag)node.getTag()).setVarExpFreeAppPred(isChild);
                }
                case VAREXP: {
                    /*List<Triple<Substitution,Substitution,HaskellExp>> pbs = new Vector<Triple<Substitution,Substitution,HaskellExp>>();
                    NarrowNode baseNarrowNode = node.getChildren().iterator().next();
                    this.buildTerms(tySubs,subs,baseNarrowNode,pbs,false,replacer,rheads);
                    for (Triple<Substitution,Substitution,HaskellExp> sse : pbs){
                        sse.z = (HaskellExp)(((Apply) (sse.z)).getFunction());
                        target.add(sse);
                    } */
                    if (node.getChildren() != null) {
                        for (NarrowNode child : node.getChildren()) {
                            isChild = this.markVarExpFreeAppPreds(child) || isChild;
                        }
                    }
                    // TODO verify
                    //return ((Tag)node.getTag()).setVarExpFreeAppPred(true);
                    return ((Tag)node.getTag()).setVarExpFreeAppPred(isChild);
                }
                case INSTANCE: {
                    InstanceAnnotation instanceAnnotation = (InstanceAnnotation)node.getAnnotation();
                    NarrowNode baseNarrowNode = instanceAnnotation.getBase();
                    for (NarrowNode child : node.getChildren()) {
                        isChild = this.markVarExpFreeAppPreds(child) || isChild;
                    }
                    return
                        ((Tag)node.getTag()).setVarExpFreeAppPred(
                            this.markVarExpFreeAppPreds(baseNarrowNode) || isChild
                        );
                }
                case PROGERROR: {
                    return false;
                }
                case FIRST:
                    for (NarrowNode child : node.getChildren()) {
                        isChild = this.markVarExpFreeAppPreds(child) || isChild;
                    }
                    return false;
                default:
                    //                throw new RuntimeException("incorrect node annotation");
            }
        }
        return false;
    }

    private HaskellEntity getEntity(String name, HaskellEntity.Sort sort) {
        return this.prelude.getEntity(this.prelude, "Prelude", name, sort);
    }

}
