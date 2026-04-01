package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Evaluator.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Swiderski
 */

public class HaskellNarrowing extends HaskellEvaluator {
    Modules modules;
    Module module;

    NarrowNode tree;
    List<NarrowNode> nodes;

    int termicount;
    int varCount;
    String varName;
    int count;

    Map<VarKey, List<Pair<Set<ClassConstraint>, HaskellSubstitution>>> casesMap;
    Map<HaskellSym, List<HaskellSubstitution>> tyInstMap;

    List<NarrowNode> startNodes;
    Set<TyConsEntity> tyConsEntities;
    private HaskellEntity errorEntity;

    GenMap genMap;
    BasicTermIndex<NarrowNode> basicTermIndex;
    NarrowNode curNode;
    List<NarrowNode> varExpNodes;
    int nodeLimit;

    HaskellObject old;
    int oldNumber;
    int appCount;
    private NarrowNode appNode;

    public Map<HaskellEntity, Integer> typeArityMap;

    public NarrowNode getFreeAppNode() {
        return this.appNode;
    }

    public HaskellNarrowing(final Modules modules, final int nodeLimit, final GenParameters genParameters) {
        this.typeArityMap = new HashMap<HaskellEntity, Integer>();
        this.modules = modules;
        this.prelude = modules.getPrelude();
        this.module = modules.getMainModule();
        this.tyConsEntities = new LinkedHashSet<TyConsEntity>();
        final Set<HaskellEntity> allTops = new HashSet<HaskellEntity>();
        for (final Module m : this.modules.getModules()) {
            allTops.addAll(m.getTopEntities());
        }
        for (final HaskellEntity e : allTops) {
            if (e instanceof TyConsEntity) {
                this.tyConsEntities.add((TyConsEntity) e);
            }
        }
        this.initEntities(allTops);
        this.errorEntity = this.prelude.getEntity(this.prelude, "Prelude", "error", HaskellEntity.Sort.VAR);
        this.tree = null;
        this.nodes = new LinkedList<NarrowNode>();
        this.varName = this.prelude.buildUniqueName();
        this.varCount = 0;
        this.genMap = new GenMap(0, 0, genParameters);
        this.basicTermIndex = new BasicTermIndex<NarrowNode>();
        this.nodeLimit = nodeLimit;
        this.termicount = 0;
        this.appCount = 4;
        final Var tyVar1 = new Var(new HaskellSym());
        final Var tyVar2 = new Var(new HaskellSym());
        final Var varapp = this.freshReplaceVar(this.prelude.buildArrow(tyVar1, tyVar2));
        final Var var = this.freshReplaceVar(tyVar1);
        final HaskellExp appTerm = (HaskellExp) this.addSubtermIDs(this.prelude.buildApply(varapp, var));
        this.appNode = new NarrowNode(appTerm, new HashSet<ClassConstraint>(), null, false, true) {
            @Override
            public boolean isRootable() {
                return false;
            }

            @Override
            public boolean isRoot() {
                return false;
            }
        };
        this.appNode.setAnnotation(new ConsAnnotation(this.appNode.getExpression(), new ArrayList<Var>()));
    }

    public int getTypeArity(final HaskellEntity e) {
        final Integer i = this.typeArityMap.get(e);
        int typeArity = 0;
        if (i == null) {
            //           TypeSchema ts = (TypeSchema) e.getType();
            final TypeSchema ts = this.modules.getAssumptions().getTypeSchemaFor(e);
            final List<HaskellType> types = this.prelude.deArrow(ts.getMatrix());
            typeArity = types.size() - 1;
            this.typeArityMap.put(e, typeArity);
        } else {
            typeArity = i.intValue();
        }
        return typeArity;
    }

    public Set<ClassConstraint> reduceConstraintsBy(final Set<ClassConstraint> ccs, final HaskellExp exp) {
        return this.reduceConstraintsBy(ccs, new HashSet<ClassConstraint>(), exp);
    }

    public Set<ClassConstraint> reduceConstraintsBy(
        final Set<ClassConstraint> ccs,
        final Set<ClassConstraint> accs,
        final HaskellExp exp)
    {
        final Set<ClassConstraint> nccs = new HashSet<ClassConstraint>(ccs);
        nccs.addAll(accs);
        this.modules.getClassConstraintGraph().reduce(nccs);

        /*
         * A class constraint could not be removed => there is no such instance
         */
        if (!ClassConstraintGraph.constraintsInWHNF(nccs)) {
            return null;
        }

        final Set<HaskellSym> varSyms = new LinkedHashSet<HaskellSym>();
        (new TypeAnnotationVarSymCollector(varSyms)).applyTo(exp);

        final Set<ClassConstraint> retCCs = new HashSet<ClassConstraint>();

        boolean changed;
        do {
            changed = false;
            for (final Iterator<ClassConstraint> cc_it = nccs.iterator(); cc_it.hasNext();) {
                final ClassConstraint cc = cc_it.next();
                final Set<HaskellSym> ccTyVars = FreeVarSymCollector.applyTo(cc.getType());
                final Set<HaskellSym> ccTyVarsIntersection = new HashSet<HaskellSym>(ccTyVars);
                ccTyVarsIntersection.retainAll(varSyms);
                if (!ccTyVarsIntersection.isEmpty()) {
                    retCCs.add(cc);
                    varSyms.addAll(ccTyVars);
                    cc_it.remove();
                    changed = true;
                }
            }
        } while (changed);

        return retCCs;
    }

    public void resetVarNames() {
        this.varCount = 0;
    }

    public String getVarName() {
        this.varCount++;
        return this.varName + this.varCount;
    }

    public void removeFromTermIndex(final NarrowNode node) {
        this.basicTermIndex.remove(node);
    }

    public void addToTermIndex(final NarrowNode node) {
        if (node.isLinkable()) {
            throw new RuntimeException("no corret annotation");
        }
        this.basicTermIndex.insert((BasicTerm) node.getExpression(), node);
    }

    public void addToGenMap(final NarrowNode node) {
        this.genMap.genInsert(node);
    }

    public void removeAllFromGenMap(final Collection<NarrowNode> nodes) {
        this.genMap.removeAll(nodes);
    }

    public List<NarrowNode> searchPossibleMoreGeneralNodes(final HaskellExp exp) {
        final List<NarrowNode> res = new LinkedList<NarrowNode>();
        this.basicTermIndex.search((BasicTerm) exp, res, false, true);
        return res;
    }

    public HaskellExp createErrorTerm(final HaskellObject obj) {
        final Var errvr = new Var(new HaskellNamedSym(this.errorEntity));
        if (!this.prelude.isSimplePrelude()) {
            final HaskellType listType = new Cons(new HaskellNamedSym(this.prelude.getList()));
            final HaskellObject listNil =
                new Cons(new HaskellNamedSym(this.prelude.getListNil())).setTypeTerm(listType);
            errvr.setTypeTerm(this.prelude.buildArrow(listType, obj.getTypeTerm()));
            return (HaskellExp) this.prelude.buildApply(errvr, listNil);
        } else {
            errvr.setTypeTerm(obj.getTypeTerm());
            return errvr;
        }
    }

    /*    public static Substitution match(HaskellExp gen,HaskellExp instance){
            return BasicTerm.Tools.matchI((BasicTerm)gen,(BasicTerm) instance);
        }*/

    public boolean moreGeneralThan(
        final Set<ClassConstraint> as,
        final Set<ClassConstraint> bs,
        final HaskellSubstitution tySubs)
    {
        final ClassConstraintGraph ccg = this.modules.getClassConstraintGraph();
        final Set<ClassConstraint> nas = new HashSet<ClassConstraint>();
        for (final ClassConstraint a : as) {
            nas.add(a.apply(tySubs));
        }
        ccg.reduce(nas);
        return (ccg.moreGeneralThan(nas, bs));
    }

    public boolean fullMatch(
        final HaskellExp aexp,
        final Set<ClassConstraint> as,
        final HaskellExp bexp,
        final Set<ClassConstraint> bs,
        final HaskellSubstitution subs,
        final HaskellSubstitution tySubs)
    {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //Collection<HaskellObject> tas = new Vector<HaskellObject>();
            //System.out.println("@@@A: "+aexp);
            //(new TypeAnnotationCollector(tas)).applyTo(aexp);
            //System.out.println("@@@B: "+bexp);
            //System.out.println("@@@@A: "+tas);
            //tas.clear();
            //(new TypeAnnotationCollector(tas)).applyTo(bexp);
            //System.out.println("@@@@B: "+tas);
        }

        if (HaskellNarrowing.matchWithTypes((BasicTerm) aexp, (BasicTerm) bexp, true, subs, tySubs)) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                // System.out.println("@@A:"+as);
                // System.out.println("@@B:"+bs);
            }
            if (this.moreGeneralThan(as, bs, tySubs)) {
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("@@@A: "+aexp);
                    //System.out.println("@@@B: "+bexp);
                    //System.out.println("@@@@@@@@@@@ fullmatch");
                }

                /*for (Map.Entry<HaskellSym,HaskellObject> entry : subs.entrySet()){
                    if (!this.hasCorrectArity(entry.getValue())) return false;
                }*/
                return true;
            }
        }
        return false;
    }

    public Pair<HaskellSubstitution, HaskellSubstitution> nodeMatch(final NarrowNode gen, final NarrowNode instance) {
        HaskellSubstitution subs = new HaskellSubstitution();
        final HaskellSubstitution tySubs = new HaskellSubstitution();
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            /*
            HaskellObject exp = gen.getExpression();
            Iterator<Apply> it = new SubTermIterator(exp);
            System.out.println("A:"+exp);
            System.out.println("A:"+gen.getConstraints());
            while (it.hasNext()){
                Apply apply = it.next();
                HaskellExp sterm = (HaskellExp) apply.getArgument();
                System.out.println("   "+sterm+" :: "+sterm.getTypeTerm());
            }

            exp = instance.getExpression();
            it = new SubTermIterator(exp);
            System.out.println("B:"+exp);
            System.out.println("B:"+instance.getConstraints());
            while (it.hasNext()){
                Apply apply = it.next();
                HaskellExp sterm = (HaskellExp) apply.getArgument();
                System.out.println("   "+sterm+" :: "+sterm.getTypeTerm());
            }
            */
        }
        if (this.fullMatch(
            gen.getExpression(),
            gen.getConstraints(),
            instance.getExpression(),
            instance.getConstraints(),
            subs,
            tySubs))
        {
            subs = subs.eliminateDuplicates();
            return new Pair<HaskellSubstitution, HaskellSubstitution>(subs, tySubs);
        }
        return null;
    }

    public static boolean equivalentWithTypes(final BasicTerm t1, final BasicTerm t2) {
        if (t1 instanceof Apply) {
            if (t2 instanceof Apply) {
                final Apply app1 = (Apply) t1;
                final Apply app2 = (Apply) t2;
                return HaskellNarrowing.equivalentWithTypes(
                    (BasicTerm) app1.getFunction(),
                    (BasicTerm) app2.getFunction())
                    && HaskellNarrowing.equivalentWithTypes(
                        (BasicTerm) app1.getArgument(),
                        (BasicTerm) app2.getArgument());
            }
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("??=A:"+t1+"|"+t1.getTypeTerm());
            //System.out.println("??=B:"+t2+"|"+t2.getTypeTerm());
        }

        if (!t1.equivalentTo(t2)) {
            return false;
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("??B=?=A type");
        }

        if ((t1.getTypeTerm().equivalentTo(t2.getTypeTerm()))) {
            return true;
        }
        /*Vector vec = new Vector();
        vec.add(t1);
        vec.add(t2);
        HaskellSym.showee(vec);*/
        return false;
    }

    public static boolean matchWithTypes(
        final BasicTerm t1,
        final BasicTerm t2,
        final boolean checkLocalVar,
        final HaskellSubstitution subs,
        final HaskellSubstitution tySubs)
    {
        /*
        if (HaskellNarrowing.equivalentWithTypes(t1,t2)) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("MWT:"+t1 + " :: "+(BasicTerm)t1.getTypeTerm());
                //System.out.println("MWT:"+t2 + " :: "+(BasicTerm)t2.getTypeTerm());
            }

                return true;
        }
        */

        if (t1 instanceof Apply) {
            if (t2 instanceof Apply) {
                final Apply app1 = (Apply) t1;
                final Apply app2 = (Apply) t2;
                return HaskellNarrowing.matchWithTypes(
                    (BasicTerm) app1.getFunction(),
                    (BasicTerm) app2.getFunction(),
                    checkLocalVar,
                    subs,
                    tySubs)
                    && HaskellNarrowing.matchWithTypes(
                        (BasicTerm) app1.getArgument(),
                        (BasicTerm) app2.getArgument(),
                        checkLocalVar,
                        subs,
                        tySubs);
            }
        }
        if (checkLocalVar) {
            if (t1 instanceof Var) {
                final HaskellSym sym = ((Atom) t1).getSymbol();
                final HaskellEntity e = sym.getEntity();
                if (e != null) {
                    if (e instanceof VarEntity) {
                        if (!(((VarEntity) e).getLocal())) {

                            if (t2 instanceof Var) {
                                final HaskellSym sym2 = ((Atom) t2).getSymbol();
                                final HaskellEntity e2 = sym2.getEntity();
                                if (e == e2) {
                                    return (BasicTerm.Tools.match(t1.getTypeTerm(), t2.getTypeTerm(), false, tySubs));
                                }

                            }
                            return false;
                        }
                    }
                }
            }
        }

        if ((t1 instanceof Cons) && (t2 instanceof Cons)) {
            if (t1.equivalentTo(t2)) {
                return (BasicTerm.Tools.match(t1.getTypeTerm(), t2.getTypeTerm(), false, tySubs));
            }
            return false;
        }

        if (t1 instanceof Var) {
            final HaskellSym sym = ((Atom) t1).getSymbol();
            final HaskellObject rep = subs.getReplaceFor(sym);

            /*
            if (checkLocalVar) {
                HaskellEntity e = sym.getEntity();
                if (e != null) {
                    if (e instanceof VarEntity){
                        if (!(((VarEntity)e).getLocal())){
                            // XXX DEBUG
                            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                                //System.out.println("LOFAILA:"+t1);
                                //System.out.println("LOFAILB:"+t2);
                            }

                            return false;
                        }
                    }
                }
            }
            */

            if (aprove.Globals.useAssertions) {
                assert ((sym.getEntity() instanceof VarEntity) && ((VarEntity) sym.getEntity()).getLocal()) : "Non local Variable!";
            }

            /*
             *
             * x :: \tau_1 (local) <-> t :: \tau_2
             *
             * if \tau_1 \tau == \tau_2
             * then
             *     subs .= {x / t}
             *     tysubs .=  \tau
             *
            */
            if (rep == null) {
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("???:"+t1+"/"+t2);
                    //System.out.println("??A:"+t1.getTypeTerm());
                    //System.out.println("??B:"+t2.getTypeTerm());
                }

                if ((BasicTerm.Tools.match(t1.getTypeTerm(), t2.getTypeTerm(), false, tySubs))) {
                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        //                    System.out.println("??OK");
                    }

                    subs.put(sym, t2);
                    return true;
                }
            } else {
                return HaskellNarrowing.equivalentWithTypes((BasicTerm) rep, t2);
            }
        }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("FAILA:"+t1);
            //System.out.println("FAILB:"+t2);
        }

        return false;
    }

    public void setIdType(final Map<Integer, HaskellObject> typeMap, final BasicTerm bt) {
        final int id = bt.getSubtermNumber();
        HaskellObject type = typeMap.get(id);
        if (type == null) {
            type = new Var(new HaskellSym());
            typeMap.put(id, type);
        }
        bt.setTypeTerm((HaskellType) type);
    }

    public HaskellObject typeRefresh(
        final HaskellObject ho,
        final Map<HaskellEntity, HaskellEntity> eMap,
        final Map<Integer, HaskellObject> typeMap)
    {
        if (ho instanceof Apply) {
            final Apply apply = (Apply) ho;
            final Apply newApply =
                new Apply(this.typeRefresh(apply.getFunction(), eMap, typeMap), this.typeRefresh(
                    apply.getArgument(),
                    eMap,
                    typeMap));
            newApply.setSubtermNumber(apply.getSubtermNumber());
            this.setIdType(typeMap, newApply);
            return newApply;
        } else if (ho instanceof Cons) {
            final Cons cons = (Cons) ho;
            final Cons newCons = new Cons(cons.getSymbol());
            newCons.setSubtermNumber(cons.getSubtermNumber());
            this.setIdType(typeMap, newCons);
            return newCons;
        } else if (ho instanceof Var) {
            final Var var = (Var) ho;
            final VarEntity e = (VarEntity) var.getSymbol().getEntity();
            Var nVar;
            if (e.getLocal()) {
                HaskellEntity ne = eMap.get(e);
                if (ne == null) {
                    ne = new VarEntity(this.getVarName(), e.getModule(), null, null, true);
                    eMap.put(e, ne);
                }
                nVar = (new Var(new HaskellNamedSym(ne)));
                nVar.setSubtermNumber(var.getSubtermNumber());
                this.setIdType(typeMap, nVar);
                return nVar;
            }
            nVar = new Var(var.getSymbol());
            nVar.setSubtermNumber(var.getSubtermNumber());
            this.setIdType(typeMap, nVar);
            return nVar;
        }
        return ho;
    }

    public HaskellObject overwritePosition(final HaskellObject exp, final List<Integer> position) {
        // Full destructive in position and exp
        final List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
        final Atom ehead = (Atom) exps.remove(0);
        if (position.isEmpty()) {
            final HaskellEntity oe = ehead.getSymbol().getEntity();
            final HaskellEntity e = new VarEntity(this.getVarName(), oe.getModule(), null, null, true);
            final Var var = new Var(new HaskellNamedSym(e));
            var.setTypeTerm(exp.getTypeTerm());
            var.setSubtermNumber(this.currentSubtermID++);
            return var;
        } else {
            final int i = position.remove(0);
            exps.set(i, this.overwritePosition(exps.get(i), position));
            return this.prelude.buildApplies(ehead, exps);
        }
    }

    public HaskellObject getExpAtPosition(final HaskellObject exp, final List<Integer> position) {
        // Full destructive in position and exp
        if (position.isEmpty()) {
            return exp;
        } else {
            final List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
            final Atom ehead = (Atom) exps.remove(0);
            final int i = position.remove(0);
            return this.getExpAtPosition(exps.get(i), position);
        }
    }

    public static HaskellExp test(final HaskellExp exp) {
        // Full destructive in position and exp
        if (((BasicTerm) exp).getSubtermNumber() < 0) {
            throw new RuntimeException("ddd");
        }
        if (exp instanceof Apply) {
            final Apply app = (Apply) exp;
            HaskellNarrowing.test((HaskellExp) app.getFunction());
            HaskellNarrowing.test((HaskellExp) app.getArgument());
        }
        return exp;
    }

    public HaskellObject placeNewVariable(final HaskellObject exp, final List<Integer> position) {
        final HaskellEntity e = new VarEntity(this.getVarName(), this.modules.getMainModule(), null, null, true);
        final Var var = new Var(new HaskellNamedSym(e));
        final HaskellObject rexp = this.getExpAtPosition(exp, position);
        var.setTypeTerm(rexp.getTypeTerm());
        var.setSubtermNumber(this.currentSubtermID);
        this.currentSubtermID++;
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("current: " + ((BasicTerm) rexp).getSubtermNumber());
        }
        return exp.visit(new SubtermReplacer(var, ((BasicTerm) rexp).getSubtermNumber()));
    }

    public HaskellObject placeNewVariableAtId(final HaskellObject exp, final int id) {
        final HaskellEntity e = new VarEntity(this.getVarName(), this.modules.getMainModule(), null, null, true);
        final Var var = new Var(new HaskellNamedSym(e));
        var.setSubtermNumber(this.currentSubtermID);
        this.currentSubtermID++;
        return exp.visit(new SubtermReplacer(var, id));
    }

    public static void removeAllUnmarked(final Collection<NarrowNode> col, final Object mark) {
        final Iterator<NarrowNode> it = col.iterator();
        while (it.hasNext()) {
            if (it.next().getMark() != mark) {
                it.remove();
            }
        }
    }

    public List<HaskellSubstitution> generateTypeInstances(final HaskellType type, final CVarEntity ve) {
        final List<HaskellObject> hs = HaskellTools.applyFlatten(type);
        final Var tyVar = (Var) hs.get(0);
        List<HaskellSubstitution> list = this.tyInstMap.get(tyVar.getSymbol());
        if (list == null) {
            list = new LinkedList<HaskellSubstitution>();
            final List<InstEntity> ies = this.classInstMap.get(ve.getParentEntity());
            if (ies != null) {
                for (final InstEntity ie : ies) {
                    HaskellType inst = Copy.deep(ie.getInstTypeTerm());
                    inst = (HaskellType) inst.visit(new AutoRenVarSubstitutor());

                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        //System.out.println("a:"+type);
                        //System.out.println("b:"+inst);
                    }

                    final HaskellSubstitution subs = BasicTerm.Tools.mgu(Copy.deep(type), Copy.deep(inst));
                    if (subs != null) {
                        list.add(new HaskellSubstitution(tyVar, (BasicTerm) subs.getReplaceFor(tyVar)));
                    }
                }
            }

            /*for (TyConsEntity tce : this.tyConsEntities){
                 HaskellObject inst = new Cons(new HaskellNamedSym(tce));
                 int arity = this.prelude.deKindArrow(((TypeSchema)tce.getType()).getMatrix()).size()-1;
                 for (int i=0; i<arity;i++){
                     inst = new Apply(inst,new Var(new HaskellSym()));
                 }
                 list.add((HaskellType)inst);
            } */
            this.tyInstMap.put(tyVar.getSymbol(), list);
        }
        return list;
    }

    public Set<ClassConstraint> checkTypeInstance(final Set<ClassConstraint> ccs, final HaskellSubstitution tySubs) {
        final ClassConstraintGraph ccg = this.modules.getClassConstraintGraph();
        final Set<ClassConstraint> nccs = new HashSet<ClassConstraint>();
        for (final ClassConstraint cc : ccs) {
            nccs.add(cc.apply(tySubs));
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("For Reduce: "+nccs);
        }

        ccg.reduce(nccs);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("--- Reduce: "+nccs);
        }

        if (ClassConstraintGraph.constraintsInWHNF(nccs)) {
            return nccs;
        }
        return null;
    }

    public List<NarrowNode> tyCaseAnalyses(
        final NarrowNode node,
        final VarEntity ve,
        final HaskellType varType,
        final HaskellType type)
    {
        final HaskellExp exp = node.getExpression();
        final Set<ClassConstraint> ccs = node.getConstraints();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("$$$:"+exp);
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            final List<HaskellObject> tas = new Vector<HaskellObject>();
            (new TypeAnnotationCollector(tas)).applyTo(exp);
            //System.out.println("$$$:"+tas);
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            final Iterator<Apply> it = new SubTermIterator(exp);
            while (it.hasNext()) {
                final Apply apply = it.next();
                final HaskellExp sterm = (HaskellExp) apply.getArgument();

                //System.out.println("   "+sterm+" :: "+sterm.getTypeTerm());
            }
        }

        final List<NarrowNode> res = new Vector<NarrowNode>();
        final TyCaseAnnotation tca = new TyCaseAnnotation(ve);
        for (final HaskellSubstitution tySubs : this.generateTypeInstances(type, (CVarEntity) ve)) {
            final Set<ClassConstraint> nccs = this.checkTypeInstance(ccs, tySubs);
            if (nccs != null) {
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("accept: "+tySubs+"  "+ve);
                }

                final HaskellExp nt = Copy.deep(exp);

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println(nt);
                }

                (new TypeAnnotationSubstitutor(tySubs)).applyTo(nt);
                this.typeChecker(nt);
                final Set<ClassConstraint> tyccs = this.reduceConstraintsBy(nccs, nt);
                if (tyccs == null) {
                    HaskellError.output(nt, "Type Case Child has unsatisfied instance in tyCaseAnalyses!");
                }
                res.add(new NarrowNode(HaskellNarrowing.test(nt), tyccs, null, true, true));
                tca.getTySubstitutions().add(tySubs);
                tca.getVarTypes().add((HaskellType) tySubs.applyTo(varType));
            }
        }
        node.setAnnotation(tca);

        // if there were any instances linking to this node, reset their instance annotation
        // and make develop process them again (by adding them again to this.nodes)
        if (node.getInstNodes() != null) {
            for (final NarrowNode instNode : node.getInstNodes()) {
                instNode.setAnnotation(null);
                instNode.setChildren(null);
                this.nodes.add(instNode);
            }
            node.setInstNodes(null);
        }

        node.resetRootable();
        node.resetLinkable();
        //HaskellSym.showee(res);
        return res;
    }

    @Override
    public Result newTermiVar(final HaskellObject exp) {
        final HaskellEntity e =
            new VarEntity("ter" + this.termicount + "m", this.modules.getMainModule(), null, null, true);
        this.termicount++;
        final Var var = new Var(new HaskellNamedSym(e));
        var.setTypeTerm(exp.getTypeTerm());
        var.setSubtermNumber(this.currentSubtermID++);
        return new TermResult(var, ((BasicTerm) exp).getSubtermNumber());
    }

    public List<NarrowNode> caseAnalyses(final NarrowNode node, final Var var) {
        final HaskellExp exp = node.getExpression();
        final Set<ClassConstraint> ccs = node.getConstraints();
        final List<NarrowNode> res = new Vector<NarrowNode>();
        if (var != null) {
            final HaskellEntity entity = var.getSymbol().getEntity();
            final VarKey vk = new VarKey(var);
            List<Pair<Set<ClassConstraint>, HaskellSubstitution>> cases = this.casesMap.get(new VarKey(var));
            if (cases == null) {
                cases = new Vector<Pair<Set<ClassConstraint>, HaskellSubstitution>>();
                this.casesMap.put(vk, cases);
                final HaskellType typeTerm = var.getTypeTerm();
                final Atom ty = (Atom) HaskellTools.getLeftMost(typeTerm);
                if (ty.getBasicSort() == BasicTerm.Sort.CONS) {
                    final TyConsEntity tyCons = (TyConsEntity) ty.getSymbol().getEntity();
                    for (final ConsEntity consEntity : tyCons.getConsList()) {
                        final Pair<Set<ClassConstraint>, List<HaskellType>> conss =
                            consEntity.getTypeTermsPer(typeTerm);
                        final Set<ClassConstraint> nccs = conss.getKey();
                        final List<HaskellType> typeTerms = conss.getValue();
                        int i = 0;
                        final List<HaskellObject> vars = new Vector<HaskellObject>();
                        for (final HaskellType tt : typeTerms) {
                            final HaskellEntity e =
                                new VarEntity(entity.getName() + i, entity.getModule(), null, null, true);
                            vars.add((new Var(new HaskellNamedSym(e))).setTypeTerm(tt));
                            i++;
                        }
                        final Cons cons = new Cons(new HaskellNamedSym(consEntity));
                        cons.setTypeTerm(this.prelude.buildArrows(typeTerms, typeTerm));
                        final HaskellObject obj = this.addSubtermIDs(this.prelude.buildApplies(cons, vars));
                        cases.add(new Pair<Set<ClassConstraint>, HaskellSubstitution>(nccs, new HaskellSubstitution(
                            var,
                            (BasicTerm) obj)));
                    }
                }
            }
            final CaseAnnotation ca = new CaseAnnotation();
            for (final Pair<Set<ClassConstraint>, HaskellSubstitution> cas : cases) {
                final HaskellSubstitution substitution = cas.getValue();
                final HaskellExp nt = (HaskellExp) substitution.applyTo((BasicTerm) exp);
                this.typeChecker(nt);
                final Set<ClassConstraint> nccs = this.reduceConstraintsBy(ccs, cas.getKey(), nt);
                if (nccs == null) {
                    // the returned instance is not a valid instance
                    continue;
                }
                res.add(new NarrowNode(HaskellNarrowing.test(nt), nccs, null, false, false));
                ca.getSubstitutions().add(substitution);
            }
            node.setAnnotation(ca);
        }
        return res;
    }

    public boolean checkConsVarTerm(final HaskellObject exp) {
        if (exp instanceof Apply) {
            final Apply app = (Apply) exp;
            return this.checkConsVarTerm(app.getFunction()) && this.checkConsVarTerm(app.getArgument());
        } else if (exp instanceof Cons) {
            return true;
        } else if (exp instanceof Var) {
            final VarEntity ve = (VarEntity) (((Var) exp).getSymbol().getEntity());
            return ve.getLocal();
        }
        return false;
    }

    public boolean checkLocalVar(final HaskellObject ehead) {
        if (ehead instanceof Var) {
            final VarEntity ve = (VarEntity) (((Var) ehead).getSymbol().getEntity());
            if (ve != null) {
                return (ve.getLocal());
            }
        }
        return false;
    }

    public Var checkExpVar(final HaskellExp exp) {
        final List<HaskellObject> hts =
            this.prelude.removeOneArrow(exp.getTypeTerm(), new Cons(this.prelude.getTypeArrowSym()));
        if (hts == null) {
            return null;
        }
        final List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
        final Atom atom = (Atom) exps.get(0);
        if (atom.getBasicSort() == BasicTerm.Sort.CONS) {
            return null;
        }
        final HaskellEntity entity = (atom).getSymbol().getEntity();
        if (exps.size() + 1 > this.appCount + this.getTypeArity(entity)) {
            return null;
        }

        final HaskellEntity e = new VarEntity(this.getVarName(), entity.getModule(), null, null, true);
        final HaskellType vt = (HaskellType) hts.get(0);
        return (Var) ((new Var(new HaskellNamedSym(e))).setTypeTerm(Copy.deep(vt)));
    }

    public HaskellObject splitConsUniVarHead(
        final HaskellObject exp,
        final List<Var> vars,
        final List<HaskellObject> subterms)
    {
        final List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
        final HaskellObject ehead = exps.remove(0);
        if ((ehead instanceof Cons) || (this.checkLocalVar(ehead) && exps.isEmpty())) {
            final ListIterator<HaskellObject> it = exps.listIterator();
            while (it.hasNext()) {
                final HaskellObject para = it.next();
                final HaskellObject npara = this.splitConsUniVarHead(para, vars, subterms);
                if (npara == null) {
                    subterms.add(para);
                    final Var var = new Var(new HaskellSym());
                    vars.add(var);
                    it.set(var);
                } else {
                    it.set(npara);
                }
            }
            return this.prelude.buildApplies(ehead, exps);
        }
        return null;
    }

    public boolean checkSplitConsOrVarStop(final NarrowNode node) {
        final List<HaskellObject> exps = HaskellTools.applyFlatten(node.getExpression());
        final Atom ehead = (Atom) exps.remove(0);
        if (this.checkLocalVar(ehead)) {
            final Set<ClassConstraint> ccs = node.getConstraints();
            node.setAnnotation(new UniVarAnnotation((Var) ehead));
            final List<NarrowNode> children = new Vector<NarrowNode>();
            for (final HaskellObject param : exps) {
                final Set<ClassConstraint> nccs = this.reduceConstraintsBy(ccs, (HaskellExp) param);
                if (nccs == null) {
                    HaskellError.output(param, "Nonexistent Instance for ParSplit(Var)!");
                }
                final NarrowNode child = new NarrowNode(HaskellNarrowing.test((HaskellExp) Copy.deep(param)), nccs, null, true, true);
                children.add(child);
            }
            if (node != this.appNode) {
                node.resetRootable();
                node.resetLinkable();
            }
            node.setChildren(children);
            return true;
        }
        final Var expVar = this.checkExpVar(node.getExpression());
        if (expVar != null) {
            ((BasicTerm) expVar).setSubtermNumber(this.currentSubtermID++);
            final Set<ClassConstraint> ccs = node.getConstraints();
            final HaskellExp exp = Copy.deep(node.getExpression());
            final HaskellExp newexp = (HaskellExp) this.prelude.buildApply(exp, expVar);
            ((BasicTerm) newexp).setSubtermNumber(this.currentSubtermID++);
            final List<NarrowNode> children = new Vector<NarrowNode>();
            final NarrowNode child = new NarrowNode(HaskellNarrowing.test(newexp), Copy.deepCol(ccs), null, true, true);
            children.add(child);
            node.setAnnotation(new VarExpAnnotation());
            node.resetRootable();
            node.resetLinkable();
            node.setChildren(children);
            this.varExpNodes.add(node);
            return true;
        }
        if (ehead instanceof Cons) {
            final List<HaskellObject> subterms = new Vector<HaskellObject>();
            final List<Var> vars = new Vector<Var>();
            final HaskellObject base = this.splitConsUniVarHead(node.getExpression(), vars, subterms);
            if (base != null) {
                final Set<ClassConstraint> ccs = node.getConstraints();
                node.setAnnotation(new ConsAnnotation(base, vars));
                final List<NarrowNode> children = new Vector<NarrowNode>();
                //if (!checkConsVarTerm(node.getExpression())){
                for (final HaskellObject subterm : subterms) {
                    final NarrowNode child =
                        new NarrowNode(HaskellNarrowing.test((HaskellExp) Copy.deep(subterm)), this.reduceConstraintsBy(
                            ccs,
                            (HaskellExp) subterm), null, true, true);
                    children.add(child);
                }
                //}
                node.setChildren(children);
                node.resetRootable();
                node.resetLinkable();
                return true;
            }
        }
        return false;
    }

    /**
     * Ensures that every path from a start node reaches an Eval-node (aka Mode.NON);
     * this is done by checking that no non-Eval path exists between start and end
     * @param start Node to start at
     * @param end Node to which no non-Eval path must exist
     * @return true, iff it will hold, that every path starting in <code>start</code> will reach an Eval node; false otherwise
     */
    public boolean evalBlockFlood(final NarrowNode start, final NarrowNode end) {
        if (start == end) {
            return false;
        }
        if (start.getMode() == Mode.NON) {
            return true;
        }
        if (start.getMode() == Mode.INSTANCE) {
            if (!this.evalBlockFlood(((InstanceAnnotation) start.getAnnotation()).getBase(), end)) {
                return false;
            }
        }

        /*
         * If we are at a leaf, then for this leaf the same argument holds, ie. no instance node must be
         * drawn if a path exists to this leaf without an Eval (aka. Mode.NON)-step.
         * Thus, if there is a possibility to link this leaf to a term above start, which would not contain an Eval node,
         * then for the leaf this instantiation will be forbidden and therefore an Eval step will be enforced.
         * Otherwise, this leaf must do an Eval-step or end with an error, which is ok, too.
         */
        if (start.getChildren() == null) {
            return true;
        }

        for (final NarrowNode node : start.getChildren()) {
            if (!this.evalBlockFlood(node, end)) {
                return false;
            }
        }
        return true;
    }

    public boolean checkInstance(final NarrowNode current) {
        if (current.isLinkable()) {
            for (final NarrowNode node : this.searchPossibleMoreGeneralNodes(current.getExpression())) {
                if ((node != current) && node.isRootable()) {
                    final Pair<HaskellSubstitution, HaskellSubstitution> subs = this.nodeMatch(node, current);
                    if (subs != null) {
                        if (this.evalBlockFlood(node, current)) {
                            //HaskellSym.showee(nodes);
                            this.connect(current, subs, node, false);
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    public NarrowNode searchInstance(final HaskellExp exp, final Set<ClassConstraint> ccs) {
        for (final NarrowNode node : this.searchPossibleMoreGeneralNodes(exp)) {

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("SIM:"+node.getExpression());
            }

            if (node.isRootable()) {
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("SIT:"+node.getExpression());
                }

                if (this.fullMatch(
                    node.getExpression(),
                    node.getConstraints(),
                    exp,
                    ccs,
                    new HaskellSubstitution(),
                    new HaskellSubstitution()))
                {
                    return node;
                }
            }
        }
        return null;
    }

    public void reduceTreeToReachables() {
        this.nodes.clear();
        final Object mark = (new TreeIterator(this.tree, this.nodes)).markAll(); // only reachables are marked
        this.genMap.removeAllUnmarked(mark);
        this.genMap.reorganize();
        final List<NarrowNode> res = new LinkedList<NarrowNode>();
        this.basicTermIndex.collectElements(res);
        for (final NarrowNode nn : res) {
            if (nn.getMark() != mark) {
                this.basicTermIndex.remove(nn);
            }
        }
    }

    public void reduceTreeViaNarrowNode(final NarrowNode viaNode) {
        final Set<NarrowNode> rmnodes = new HashSet<NarrowNode>();
        final Iterator<NarrowNode> it = (new TreeIterator(this.tree, true));

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("### Instances: ");
        }

        while (it.hasNext()) {
            final NarrowNode iNarrowNode = it.next();
            if (viaNode != iNarrowNode) {
                if (iNarrowNode.isLinkable() || (iNarrowNode.getMode() == Mode.INSTANCE)) {
                    final Pair<HaskellSubstitution, HaskellSubstitution> subs = this.nodeMatch(viaNode, iNarrowNode);
                    if (subs != null) {
                        this.disconnect(iNarrowNode);
                        this.connect(iNarrowNode, subs, viaNode, true);
                    }
                    rmnodes.add(iNarrowNode);
                }
            }
        }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println();
        }

        this.removeAllFromGenMap(rmnodes);
    }

    public NarrowNode createNewNarrowNode(final HaskellExp generalisation, final Set<ClassConstraint> gencs) {
        //generalisation = (HaskellExp) this.addSubtermIDs(Copy.deep(generalisation));

        if (gencs == null) {
            HaskellError.output(generalisation, "Unsatisfied Instances in createNewNarrowNode!");
        }

        NarrowNode generalisationNarrowNode = this.searchInstance(generalisation, gencs);
        if (generalisationNarrowNode == null) {
            generalisationNarrowNode = new NarrowNode(HaskellNarrowing.test(generalisation), gencs, null, true, true);
            this.nodes.add(generalisationNarrowNode);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("### real new genNode: "+generalisationNarrowNode);
            }

            this.basicTermIndex.insert((BasicTerm) generalisationNarrowNode.getExpression(), generalisationNarrowNode);
        } else {
            final Vector<Object> vec = new Vector<Object>();
            vec.add(this);
            vec.add(generalisation.toString());
            vec.add(generalisationNarrowNode);
            //            vec.add(genNarrowNodes);
            //            HaskellSym.showee(vec);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("### gen searchInstance: "+generalisationNarrowNode);
            }
        }
        this.reduceTreeViaNarrowNode(generalisationNarrowNode);
        this.reduceTreeToReachables();
        this.addToGenMap(generalisationNarrowNode);
        return generalisationNarrowNode;
    }

    public void generalisation(final GenSet genNodes) {
        HaskellExp exp = Copy.deep(genNodes.iterator().next().getExpression());

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("### Cur Exp: "+(new PLAIN_Util()).haskellObject(exp,this.module));
            //System.out.println("### Gen Pos: "+genNodes.getPosition());
        }

        //exp = (HaskellExp) this.addSubtermIDs(this.overwritePosition(Copy.deep(exp),genNodes.getPosition()));
        HaskellNarrowing.test(exp);
        final BasicTerm rep = (BasicTerm) this.getExpAtPosition(exp, genNodes.getPosition());
        final int id = rep.getSubtermNumber();
        exp = (HaskellExp) this.placeNewVariableAtId(exp, id);

        this.generalisationExp(exp, id);
    }

    public NarrowNode generalisationExp(HaskellExp exp, final int id) {
        this.modules.setAssumptions((new Assumptions.MapSkeleton()).autoQuanCopy((Assumptions.MapSkeleton) this.modules
            .getAssumptions()));

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("### rfrGen: "+exp);
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //Iterator<Apply> it = new SubTermIterator(exp);
            //while (it.hasNext()){
            //Apply apply = it.next();
            //System.out.println(apply +" :: "+apply.getTypeTerm());
            //System.out.println(apply.getFunction().getTypeTerm()+"%%"+apply.getArgument().getTypeTerm());
            //}
        }

        exp =
            (HaskellExp) this.typeRefresh(
                exp,
                new HashMap<HaskellEntity, HaskellEntity>(),
                new HashMap<Integer, HaskellObject>());

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("### rrGen Exp: "+(new PLAIN_Util()).haskellObject(exp,this.module));
        }

        // XXX DEBUG timing information
        //        long preCheckBasicTermMillis = System.currentTimeMillis();
        final TypeSchema ts = (TypeSchema) this.modules.checkBasicTerm(exp);
        final Set<ClassConstraint> ccs = ts.getConstraints();
        HaskellNarrowing.test(exp);
        //        System.err.println("NARROWING: checkBasicTerm+test in generalisationExp took "+((System.currentTimeMillis()-preCheckBasicTermMillis)/1000d)+" sec");
        //        System.err.println("NARROWING: exp: "+exp+"\n\n");

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.print("### GenNodes ");
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println(node.num+" ");
            //System.out.println();
        }

        /*Vector vec = new Vector();
        vec.add(this.genMap);
        vec.add(genNodes);
        vec.add(this);*/
        return this.createNewNarrowNode(exp, ccs);
    }

    public boolean checkGeneralisations(final NarrowNode current) {
        final GenSet genNodes = this.genMap.genInsert(current);
        if (genNodes != null) {
            this.generalisation(genNodes);
            return true;
        }
        return false;
    }

    public Var freshReplaceVar(final HaskellType type) {
        final HaskellEntity e = new VarEntity(this.getVarName(), this.module, null, null, true);
        final Var var = (Var) ((new Var(new HaskellNamedSym(e))).setTypeTerm(type));
        var.setSubtermNumber(this.currentSubtermID);
        this.currentSubtermID++;
        return var;
    }

    @Override
    public Result checkRedex(
        final boolean top,
        final HaskellObject ehead,
        final HaskellObject redex,
        final List<HaskellObject> exps)
    {
        final Var hvar = (Var) ehead;
        if (((VarEntity) hvar.getSymbol().getEntity()).getLocal()) {
            return new GenResult(this.freshReplaceVar(redex.getTypeTerm()), redex);
        }
        final int typeArity = this.getTypeArity(hvar.getSymbol().getEntity());
        if (typeArity + this.appCount < exps.size()) {
            if (!top) {
                return new GenResult(this.freshReplaceVar(redex.getTypeTerm()), redex);
            } else {
                return new UnapplyResult();
            }
        }
        return null;
    }

    public HaskellExp checkSubInstances(final HaskellExp cur, final Set<ClassConstraint> ccs) {
        boolean found = false;
        final HaskellExp itest = Copy.deep(cur);
        final Iterator<Apply> it = new SubTermIterator(itest);
        while (it.hasNext()) {
            final Apply apply = it.next();
            final HaskellExp sterm = (HaskellExp) apply.getArgument();

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("SI:"+sterm);
            }

            final Set<ClassConstraint> stccs = this.reduceConstraintsBy(ccs, sterm);
            if (stccs == null) {
                HaskellError.output(sterm, "Subterm has unsatisfied instance in checkSubInstances!");
            }
            if (this.searchInstance(sterm, stccs) != null) {
                final HaskellEntity e = new VarEntity(this.getVarName(), this.module, null, null, true);
                final Var var = new Var(new HaskellNamedSym(e));
                var.setTypeTerm(sterm.getTypeTerm());
                var.setSubtermNumber(this.currentSubtermID);
                this.currentSubtermID++;
                apply.setArgument(var);
                found = true;
            }
        }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("### checkSubInstances for "+cur);
        }

        if (found) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("### found Generalisation: "+itest);
            }
        }
        return found ? itest : null;
    }

    public List<NarrowNode> addNextChildrenTo(final NarrowNode node) {
        List<NarrowNode> children = null;
        if (node.getMode() == Mode.PROGERROR) {
            children = new Vector<NarrowNode>();
        } else {
            final HaskellExp cur = node.getExpression();
            final Set<ClassConstraint> ccs = node.getConstraints();
            if (cur == null) {
                children = this.startNodes;
            } else {
                HaskellNarrowing.test(cur);
                if (this.checkSplitConsOrVarStop(node) || this.checkInstance(node)) {
                    return node.getChildren();
                }
                if (node.isRootable()) {
                    this.basicTermIndex.insert((BasicTerm) node.getExpression(), node);
                }
                if (node.isLinkable()) {
                    if (this.checkGeneralisations(node)) {
                        return null;
                    }
                    final HaskellExp genExp = this.checkSubInstances(cur, ccs);
                    if (genExp != null) {
                        this.createNewNarrowNode(genExp, this.reduceConstraintsBy(ccs, genExp));
                        return null;
                    }
                }
                this.typeChecker(cur);

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //Collection<HaskellObject> tas = new Vector<HaskellObject>();
                    //(new TypeAnnotationCollector(tas)).applyTo(cur);
                    //System.out.println("@@@@A: "+tas);
                    //System.out.println("@@@@CC:"+ccs);
                }
                final Result res = this.evaluate(cur);
                switch (res.getKind()) {
                case TYCASE:
                    final int id = ((TyCaseResult) res).getSubtermID();
                    if (id != ((BasicTerm) cur).getSubtermNumber()) {
                        final boolean bold = node.isLinkable();
                        node.setLinkable();
                        final HaskellExp nexp = (HaskellExp) this.placeNewVariableAtId(Copy.deep(cur), id);

                        HaskellExp nexpScratch = Copy.deep(nexp);
                        this.modules.setAssumptions((new Assumptions.MapSkeleton())
                            .autoQuanCopy((Assumptions.MapSkeleton) this.modules.getAssumptions()));
                        nexpScratch =
                            (HaskellExp) this.typeRefresh(
                                nexpScratch,
                                new HashMap<HaskellEntity, HaskellEntity>(),
                                new HashMap<Integer, HaskellObject>());

                        // XXX DEBUG timing information
                        //                                      long preCheckBasicTermMillis = System.currentTimeMillis();

                        final TypeSchema ts = (TypeSchema) this.modules.checkBasicTerm(nexpScratch);

                        // XXX DEBUG timing information
                        //                                      System.err.println("checkBasicTerm in addNextChildrenTo (TYCASE) took "+((System.currentTimeMillis()-preCheckBasicTermMillis)/1000d)+" sec");

                        final Result tyRes = this.evaluate(nexpScratch);
                        if (tyRes.getKind() != ResultKind.TYCASE) {
                            final NarrowNode gnode = this.generalisationExp(nexp, id);
                            if (!bold) {
                                node.resetLinkable();
                            }

                            if (cur == this.old) {
                                System.err.println("cur (3rd line below) is old!");
                                System.err.println(id);
                                final Vector<Object> vec = new Vector<Object>();
                                vec.add(cur);
                                vec.add(ccs);
                                System.err.println(ccs);
                                System.err.println(cur);
                                vec.add(nexp);
                                vec.add(gnode.getConstraints());
                                System.err.println(gnode.getConstraints());
                                System.err.println(gnode.getExpression());
                                System.err.println("Old Node Number: " + this.oldNumber);
                                System.err.println("Node Number: " + node.num);
                                //DottyGraphArea.showDialog("WTF", new NarrowingGraphToDOT(this.modules).buildDOT(this.tree), true);
                                //HaskellSym.showee(vec);
                            }
                            this.old = cur;
                            this.oldNumber = node.num;

                            return null;
                        }
                    }
                    children =
                        this.tyCaseAnalyses(
                            node,
                            ((TyCaseResult) res).getVarEntity(),
                            ((TyCaseResult) res).getVarType(),
                            ((TyCaseResult) res).getType());
                    break;
                case CASE:
                    children = this.caseAnalyses(node, ((CaseResult) res).getVariable());
                    break;
                case TERM:
                    children = new Vector<NarrowNode>();
                    final HaskellExp nexp = (HaskellExp) ((TermResult) res).getTerm();
                    this.typeChecker(nexp);
                    final TermResult tres = (TermResult) res;
                    node.setEvalSubtermID(tres.getSubtermID());
                    children.add(new NarrowNode(HaskellNarrowing.test(nexp), this.reduceConstraintsBy(ccs, nexp), null, true, true));
                    break;
                case UNAPPLY:
                    final Pair<HaskellSubstitution, HaskellSubstitution> subs = this.nodeMatch(this.appNode, node);
                    if (subs == null) {
                        throw new RuntimeException("appTerm does not match");
                    }
                    this.connect(node, subs, this.appNode, false);
                    return node.getChildren();
                case GENERALIZE:
                    final HaskellExp iexp = (HaskellExp) ((GenResult) res).getTerm();
                    //iexp = (HaskellExp) this.addSubtermIDs(iexp);

                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        //System.out.println("### Instances Exp: "+iexp);
                    }

                    final boolean old = node.isLinkable();
                    node.setLinkable();
                    final NarrowNode helper = this.createNewNarrowNode(iexp, this.reduceConstraintsBy(ccs, iexp));
                    if (!old) {
                        node.resetLinkable();
                    }
                    return node.getChildren();
                case ERROR:
                    children = new Vector<NarrowNode>();
                    children.add(new NarrowNode(
                        (HaskellExp) this.addSubtermIDs(this.createErrorTerm(cur)),
                        new HashSet<ClassConstraint>(),
                        new ProgErrorAnnotation(),
                        false,
                        false));
                    break;
                case FINISH:
                    children = new Vector<NarrowNode>();
                    break;
                }
            }
        }
        node.setChildren(children);
        return children;
    }

    public void connect(
        final NarrowNode from,
        final Pair<HaskellSubstitution, HaskellSubstitution> subsPair,
        final NarrowNode to,
        final boolean addChildren)
    {
        final HaskellSubstitution subs = subsPair.x;
        final HaskellSubstitution tySubs = subsPair.y;
        final List<NarrowNode> children = new Vector<NarrowNode>();
        final List<Var> vars = new Vector<Var>();
        for (final Map.Entry<HaskellSym, HaskellObject> entry : subs.entrySet()) {
            vars.add(new Var(entry.getKey()));
            final HaskellExp iexp = (HaskellExp) entry.getValue();
            final Set<ClassConstraint> ccs = this.reduceConstraintsBy(from.getConstraints(), iexp);
            if (ccs == null) {
                HaskellError.output(iexp, "Subterm of Ins-node has unsatisfied instance in connect!");
            }
            children.add(new NarrowNode(HaskellNarrowing.test(Copy.deep(iexp)), ccs, null, true, true));
        }
        if (addChildren) {
            this.nodes.addAll(children);
        }
        from.setChildren(children);
        from.setAnnotation(new InstanceAnnotation(to, vars, tySubs));
        from.resetLinkable();
        to.addInstNode(from);
    }

    public void disconnect(final NarrowNode from) {
        if (from.getMode() == Mode.INSTANCE) {
            final InstanceAnnotation ia = (InstanceAnnotation) from.getAnnotation();
            ia.getBase().removeInstNode(from);
        }
    }

    public void correctVarExpNodes() {
        for (final NarrowNode ven : this.varExpNodes) {
            final NarrowNode expNode = ven.getChildren().get(0);
            if (!expNode.isRoot()) {
                boolean makeRoot = false;
                switch (expNode.getMode()) {
                case NON:
                    makeRoot = true;
                    break;
                case TYCASE:
                    makeRoot = false;
                    break; // matraf -- was: makeRoot = true;  break;
                case CASE:
                    makeRoot = true;
                    break;
                case INSTANCE:
                    makeRoot = false;
                    break;
                case VAREXP:
                    makeRoot = false;
                    break;
                case PROGERROR:
                    makeRoot = false;
                    break;
                case CONS:
                    makeRoot = false;
                    break;
                case UNIVAR:
                    makeRoot = false;
                    break;
                case FIRST:
                    makeRoot = false;
                    break;
                default:
                    makeRoot = false;
                    break;
                }
                if (makeRoot) {
                    /*
                     * makes a root node out of Eval, Case, and TyCase nodes
                     * this is used in NarrowNode.isRoot(), since this is only
                     * valid if at least one one node points at it
                     * This will be used in the analysis of DPs, since there edges are drawn only between isRoot() nodes
                     */
                    expNode.setRootable();
                    expNode.addInstNode(expNode);
                }
            }
        }
    }

    public NarrowNode develop(final List<Pair<HaskellObject, HaskellExp>> typedTerms, final Abortion aborter)
        throws AbortionException
    {
        this.startNodes = new Vector<NarrowNode>();
        for (final Pair<HaskellObject, HaskellExp> typedTerm : typedTerms) {
            HaskellExp exp = ((QuantorExp) typedTerm.getValue()).getResult();
            final Set<ClassConstraint> constraints = ((TypeSchema) (typedTerm.getKey())).getConstraints();
            //Substitution subs = new Substitution();
            exp = (HaskellExp) this.addSubtermIDs(exp);
            //exp = (HaskellExp)subs.applyToWithSubtermNumbering((BasicTerm)exp, this.currentSubtermID);
            //this.currentSubtermID = subs.getNewSubtermIDMax();
            this.startNodes.add(new NarrowNode(HaskellNarrowing.test(exp), constraints, null, true, true));
        }

        this.varExpNodes = new Vector<NarrowNode>();
        this.casesMap = new HashMap<VarKey, List<Pair<Set<ClassConstraint>, HaskellSubstitution>>>();
        this.tyInstMap = new HashMap<HaskellSym, List<HaskellSubstitution>>();
        this.tree = new NarrowNode(null, null, new FirstAnnotation(), false, false);
        this.nodes.add(this.tree);
        int i = 0;
        //HaskellSym.showee(this);
        while (!this.nodes.isEmpty()) {
            //HaskellSym.showee(this);
            aborter.checkAbortion();
            i++;

            /*
            if (i % 100 == 0) {
                    String dotString = new NarrowingGraphToDOT(this.modules).buildDOT(this.tree);
                    DottyGraphArea.showDialog("Narrowing Graph #"+i, dotString, true, DottyGraphArea.DisplayPanelType.PICCOLO_WRAPPER);
                    */

            /*
            HaskellSym.showee(tree);
            try {
                Writer writer = new FileWriter("/home/swiste/tmpfile"+i+".dot");
                        String dotString = new NarrowingGraphToDOT(this.modules).buildDOT(this.tree);
                        //DottyGraphArea.showDialog("Narrowing Graph #"+i, dotString, true, DottyGraphArea.DisplayPanelType.PICCOLO_WRAPPER);
                writer.write(dotString);
                writer.close();
            } catch (Exception e){
                System.err.println(e.getMessage());
                e.printStackTrace();
            }
            */
            //}

            if (i > this.nodeLimit) {
                return null;
            }
            final NarrowNode current = this.nodes.remove(0);
            this.curNode = current;
            final List<NarrowNode> children = this.addNextChildrenTo(current);
            if (children != null) {
                this.nodes.addAll(children);
            }
            /*         // XXX DEBUG
                       if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {

                          System.out.println("###"+i+" Current Node:" );
                        System.out.println("  "+current);
                        System.out.println("###"+i+" Current Tree:" );
                        Iterator<NarrowNode> it = new TreeIterator(this.tree,true);
                        while(it.hasNext()){
                        NarrowNode node = it.next();
                        System.out.println("  "+node);
                        }
                        System.out.println("###"+i+" GenMap contains:");
                        Set<NarrowNode> tnodes = new HashSet<NarrowNode>();
                        this.genMap.getAll(tnodes);
                        for (NarrowNode node : tnodes){
                        System.out.print(node.num+" ");
                        }
                        System.out.println();
                        System.out.println("###"+i+" Index  contains:");
                        Set<NarrowNode> ttnodes = new HashSet<NarrowNode>();
                        this.basicTermIndex.collectElements(ttnodes);
                        for (NarrowNode node : ttnodes){
                        System.out.print(node.num+" ");
                        }
                        System.out.println();
                        System.out.println("###"+i+" Nodes contains:");
                        for (NarrowNode node : this.nodes){
                        System.out.print(node.num+" ");
                        }
                        System.out.println();
                        if (j == 0) {
                        Graph<NarrowNode,String> graph = buildGraph();
                        HaskellSym.showGraphee(graph);
                        j = 100;
                        } else {
                        j--;
                        }
                       }
                        */
        }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("Nodes: "+i);
        }

        this.correctVarExpNodes();
        return this.tree;
    }

    public static int ecount = 0;

}
