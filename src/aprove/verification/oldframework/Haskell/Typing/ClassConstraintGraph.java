package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author Stephan Swiderski
 * @version $Id$ The ClassConstraintGraph represents the class hierachie in a HaskellProgram An Example of a hierachie
 * (from Prelude): <br/>
 * Num a -> Ord a -> Eq a <br/>
 * IO a -> Monad a </br> Eq is a superclass of Ord, Ord is a superclass of Num and so Eq is also a superclass of Num <br/>
 * Also it contains the instance reduction rules for class constraints Example: Eq (List (Maybe a)) -> Eq (Maybe a)
 * (with rule Eq (List b) -> Eq b)
 */
public class ClassConstraintGraph extends HaskellDepGraph implements HaskellBean {
    Set<ClassConstraintRule> rules;
    public HaskellEntity num;

    private Map<TyClassEntity, Set<ClassConstraintRule>> class2rules;

    private Set<Pair<TyClassEntity, TyConsEntity>> unusableInstances;

    public ClassConstraintGraph() {
        this.class2rules = null;
        this.rules = new HashSet<ClassConstraintRule>();
        this.unusableInstances = new HashSet<Pair<TyClassEntity, TyConsEntity>>();
    }

    public Set<ClassConstraintRule> getRulesForClass(final TyClassEntity tce) {
        // adding the rules to the cache
        if (this.class2rules == null) {
            this.class2rules = new HashMap<TyClassEntity, Set<ClassConstraintRule>>();
            for (final ClassConstraintRule ccr : this.rules) {
                Set<ClassConstraintRule> classRules = this.class2rules.get(ccr.getPattern().getTyClass().getEntity());
                if (classRules == null) {
                    classRules = new HashSet<ClassConstraintRule>();
                    this.class2rules.put((TyClassEntity) ccr.getPattern().getTyClass().getEntity(), classRules);
                }
                classRules.add(ccr);
            }
        }
        return this.class2rules.get(tce);
    }

    public void addRule(final ClassConstraintRule ccr) {
        this.class2rules = null;
        this.rules.add(ccr);
    }

    public Set<ClassConstraintRule> getRules() {
        return this.rules;
    }

    /*
    public void setRules(Set<ClassConstraintRule> rules) {
        this.rules = rules;
    }
    */

    public void setNum(final HaskellEntity num) {
        this.num = num;
    }

    public HaskellEntity getNum() {
        return this.num;
    }

    /**
     * @param start subclass
     * @param end superclass
     */
    public void addEdge(final ClassConstraint start, final ClassConstraint end) {
        this.addEdge(start.getTyClass().getEntity(), end.getTyClass().getEntity());
    }

    /**
     * @param start subclass
     * @param end superclass
     * @return true, iff start is a subclass of end, and the type terms of both constraints are equal
     */
    public boolean pathFromTo(final ClassConstraint start, final ClassConstraint end) {
        if (start.getType().equivalentTo(end.getType())) {
            return this.pathFromTo(start.getTyClass().getEntity(), end.getTyClass().getEntity());
        }
        return false;
    }

    public void setNumTyClass(final HaskellEntity num) {
        this.num = num;
        if (!num.getName().equals("Num")) {
            throw new RuntimeException();
        }
    }

    /**
     * checks if a class of the given constraint is a subclass of the num-class (needed for the default-rule)
     */
    public boolean isNumSubClass(final ClassConstraint start) {
        final ClassConstraint end =
            new ClassConstraint(new HaskellNamedSym("Prelude", "Num", this.num), start.getType());
        return this.pathFromTo(start, end);
    }

    /**
     * reduces the set of class constraint by appling the three standard reductions: equivalence, instance and subclass
     * reduction as long as they at least one of them makes a change
     */
    public void reduce(final Set<ClassConstraint> cs) {
        boolean change;
        do {
            change = ClassConstraintGraph.applyEquivalenceReduction(cs);
            change = this.applyInstanceReduction(cs) || change;
            change = this.applySubClassReduction(cs) || change;
        } while (change);
    }

    /**
     * (..., C t, C t, ...) =====> (...,C t,...)
     */
    public static boolean applyEquivalenceReduction(final Set<ClassConstraint> ccs) {
        boolean change = false;
        final Iterator<ClassConstraint> it = ccs.iterator();
        Outer: while (it.hasNext()) {
            final ClassConstraint zcc = it.next();
            for (final ClassConstraint cc : ccs) {
                if ((cc != zcc) && zcc.equivalentTo(cc)) {
                    it.remove();
                    change = true;
                    continue Outer;
                }
            }
        }
        return change;
    }

    /**
     * (...,A t,B t,...) =====> (...,B t,....), if B is subclass of A
     */
    public boolean applySubClassReduction(final Set<ClassConstraint> ccs) {
        boolean change = false;
        final Iterator<ClassConstraint> it = ccs.iterator();
        Outer: while (it.hasNext()) {
            final ClassConstraint zcc = it.next();
            for (final ClassConstraint cc : ccs) {
                if ((cc != zcc) && this.pathFromTo(cc, zcc)) {
                    it.remove();
                    change = true;
                    continue Outer;
                }
            }
        }
        return change;
    }

    /**
     * (...,A (TyCons a1 .. am),....) =====> (...,B1 ai1,...,Bn ain,....) <br/>
     * if Class A has an instance for TyCons of this form (n,m == 0 is allowed) instance (B1 ai1,...,Bn ain) => A
     * (TyCons a1 .. am) for ij in {1...n} example: instance Eq a => Eq (List a) where so ( ..., Eq (List a),...) =====>
     * (..., Eq a, ....)
     */
    public boolean applyInstanceReduction(final Set<ClassConstraint> ccs) {
        boolean change = false;
        for (final ClassConstraintRule ccr : this.rules) {
            final ClassConstraint cc = ccr.getPattern();
            final TyClassEntity classEntity = (TyClassEntity) cc.getTyClass().getEntity();
            final TyConsEntity typeConsEntity =
                (TyConsEntity) ((Atom) HaskellTools.getLeftMost(cc.getType())).getSymbol().getEntity();
            if (this.unusableInstances.contains(new Pair<TyClassEntity, TyConsEntity>(classEntity, typeConsEntity))) {
                continue; // do not use unusable rules
            }
            change = ccr.applyTo(ccs) || change;
        }
        return change;
    }

    /**
     * returns true, if the constraints in gcs are more or equally general than the constraints of ccs, Examples: <br/>
     * () is more general than (Num a) <br/>
     * (Ord a) is more general than (Num a) <br/>
     * (Eq a) is more general than (Ord a,Num a) <br/>
     * (Num a) is more general than (Ord a,Num a) <br/>
     * (Num a) is more general than (Num a) <br/>
     */
    public boolean moreGeneralThan(final Set<ClassConstraint> gcs, final Set<ClassConstraint> ccs) {
        OuterLoop: for (final ClassConstraint gencc : gcs) {
            for (final ClassConstraint cc : ccs) {
                if (this.pathFromTo(cc, gencc)) {
                    continue OuterLoop;
                }
            }
            return false;
        }
        return true;
    }

    /**
     * returns the set of superClassSymbols of the class given as symbol
     */
    public Set<HaskellSym> getSuperClassesOf(final HaskellSym sym) {
        final Set<HaskellSym> syms = new HashSet<HaskellSym>();
        try {
            final Node<HaskellEntity> node = this.getNodeFromObject(sym.getEntity());
            final Set<Node<HaskellEntity>> nodes = new HashSet();
            nodes.add(node);
            final Set<Node<HaskellEntity>> sclns = this.determineReachableNodes(nodes);
            for (final Node<HaskellEntity> scln : sclns) {
                final HaskellEntity scl = scln.getObject();
                if (sym.getEntity() != scl) {
                    syms.add(new HaskellNamedSym(scl.getModule().getName(), scl.getName(), scl));
                }
            }
        } catch (final NullPointerException e) {
            HaskellSym.showee(sym);
            throw e;
        }
        return syms;
    }

    /**
     * checks if all needed instances are defined Example: instance Ord (MyType a) where {..} so instance Eq (MyType a)
     * where {..} is needed because class Eq a => Ord a and also it checks if then constraints of the instance for the
     * base class are satisfied.
     */
    public void checkInstances() {
        for (final ClassConstraintRule ccr : this.rules) {
            final ClassConstraintRule fccr = ccr.freshVarCopy();
            final ClassConstraint cc = fccr.getPattern();
            this.checkForSimpleConstraints(ccr.getResults(), cc.getTyClass().getEntity().getValue());
            final HaskellType instance = cc.getType();
            for (final HaskellSym sym : this.getSuperClassesOf(cc.getTyClass())) {
                final Set<ClassConstraint> ccs = new HashSet<ClassConstraint>();
                ccs.add(new ClassConstraint(sym, Copy.deep(instance)));
                if (!this.applyInstanceReduction(ccs)) {
                    HaskellSym.showee(sym);
                    HaskellError.output(cc.getTyClass().getEntity().getValue(), "instance " + instance + " for class "
                        + sym.getEntity().getName() + " missing");
                }
                this.reduce(ccs);
                if (!this.moreGeneralThan(ccs, fccr.getResults())) {
                    HaskellError.output(cc.getTyClass().getEntity().getValue(), "instance " + instance + " for class "
                        + sym.getEntity().getName() + " missing");
                }
            }
        }
    }

    /**
     * checks if a set of constraints is in WHNF and if not, this fact is interpreted as absence of an instance for this
     * constraint example: Eq (List a) is not in WHNF so instance Eq (List a) is missing cause the InstanceReduction
     * could not reduce this constraint to a WHNF
     */
    public void checkConstraints(final Set<ClassConstraint> ccs, final HaskellObject ho) {
        for (final ClassConstraint cc : ccs) {
            if (HaskellTools.getLeftMost(cc.getType()) instanceof Cons) {
                HaskellError.output(ho, "instance " + cc + " missing");
            }
        }
    }

    /**
     * checks if a set of constraints is simple a constraint is only simple if the type is a type variable (Hugs report,
     * context free syntax) example: Eq a is simple Eq (m a) is not simple ho is the errorpoint in code
     */
    public void checkForSimpleConstraints(final Set<ClassConstraint> ccs, final HaskellObject ho) {
        for (final ClassConstraint cc : ccs) {
            if (!(cc.getType() instanceof Var)) {
                HaskellError.output(ho, "illegal constraint " + cc + " in class or instance head");
            }
        }
    }

    /**
     * checks that classes do not depend on each other // * cycles of size 1 are not considered, since these are
     * self-loops which we introduced
     */
    public void checkAcyclic() {
        for (final Cycle<HaskellEntity> cyc : this.getSCCs()) {
            if (cyc.size() > 0) {
                String names = "";
                String s = "";
                for (final HaskellEntity he : cyc.getNodeObjects()) {
                    names += s + (he.getName());
                    s = ", ";
                }
                HaskellError.output(cyc.getNodeObjects().iterator().next(),
                    "the following classes depend on each other: " + names);
            }
        }
    }

    /**
     * checks if a set of constraints is in WHNF a constraint is in WHNF if its types head symbol is not a type
     * constructor example: Eq (List a) is not WHNF Eq (m a) is in WHNF Eq a is in WHNF
     */
    public static boolean constraintsInWHNF(final Set<ClassConstraint> ccs) {
        for (final ClassConstraint cc : ccs) {
            if (HaskellTools.getLeftMost(cc.getType()) instanceof Cons) {
                return false;
            }
        }
        return true;
    }

    /**
     * allows visiting this Graph
     */
    public HaskellObject visit(final HaskellVisitor hv) {
        this.class2rules = null;
        this.rules = hv.listWalk(this.rules, hv);
        this.num = hv.walk(this.num, hv);
        return null;
    }

    /**
     * needs special deepcopy
     */
    public ClassConstraintGraph entityCopy(final Map<HaskellObject, HaskellObject> eMap) {
        final ClassConstraintGraph ccg = new ClassConstraintGraph();
        ccg.rules = Copy.deepCol(this.rules);

        // copy the unusable instances based on the replacement map
        ccg.unusableInstances = new HashSet<Pair<TyClassEntity, TyConsEntity>>(this.unusableInstances.size());
        for (final Pair<TyClassEntity, TyConsEntity> unusableInstance : this.unusableInstances) {
            final TyClassEntity newUnusableInstanceClassEntity = (TyClassEntity) eMap.get(unusableInstance.x);
            final TyConsEntity newUnusableInstanceTypeConsEntity = (TyConsEntity) eMap.get(unusableInstance.y);
            if ((newUnusableInstanceClassEntity == null) || (newUnusableInstanceTypeConsEntity == null)) {
                throw new RuntimeException("replacement not found!");
            }
            ccg.unusableInstances.add(new Pair<TyClassEntity, TyConsEntity>(newUnusableInstanceClassEntity,
                newUnusableInstanceTypeConsEntity));
        }

        ccg.num = this.num;
        ccg.entityCopy(this, eMap);
        return ccg;
    }

    /**
     * sometimes a HaskellProgram is reduced to the needs of some startterms and with this methode some classes and
     * instances could be removed
     */
    public void removeEntities(final Collection<HaskellEntity> entities) {
        this.class2rules = null;
        final Map<TyClassEntity, List<InstEntity>> class2RemovedInstEntities = new HashMap<TyClassEntity, List<InstEntity>>();
        for (final HaskellEntity e : entities) {
            // save the InstEntities, so that we can use them later to reduce the rules
            if (e instanceof InstEntity) {
                final InstEntity ie = (InstEntity) e;
                List<InstEntity> ies = class2RemovedInstEntities.get(ie.getTyClassEntity());
                if (ies == null) {
                    ies = new ArrayList<InstEntity>();
                    class2RemovedInstEntities.put((TyClassEntity) ie.getTyClassEntity(), ies);
                }
                ies.add(ie);
            }

            final Node<HaskellEntity> node = this.getNodeFromObject(e);
            if (node != null) {
                final Set<Node<HaskellEntity>> iNodes = this.getIn(node);
                final Set<Node<HaskellEntity>> oNodes = this.getOut(node);
                if ((iNodes != null) && (oNodes != null)) {
                    for (final Node<HaskellEntity> ino : iNodes) {
                        for (final Node<HaskellEntity> ono : oNodes) {
                            this.addEdge(ino, ono);
                        }
                    }
                }
                this.removeNode(node);
            }
        }
        final Iterator<ClassConstraintRule> it = this.rules.iterator();
        while (it.hasNext()) {
            final ClassConstraintRule ccr = it.next();
            final ClassConstraint cc = ccr.getPattern();
            if (entities.contains(cc.getTyClass().getEntity())) {
                it.remove();
            } else {
                final List<HaskellObject> hos = HaskellTools.applyFlatten(cc.getType());
                final TyConsEntity tyConsEntity = (TyConsEntity) ((Atom) hos.get(0)).getSymbol().getEntity();

                boolean isThisInstance = false;
                final List<InstEntity> removedInstEntities = class2RemovedInstEntities.get(cc.getTyClass().getEntity());
                if (removedInstEntities != null) {
                    for (final InstEntity ie : removedInstEntities) {
                        isThisInstance =
                            (ie.getTyClassEntity() == cc.getTyClass().getEntity())
                                && (ie.getTyConsEntity() == tyConsEntity);
                        if (isThisInstance)
                         {
                            break; // we have found this instance, i.e. it must not be used anymore
                        }
                    }
                }

                if ((isThisInstance) || (entities.contains(tyConsEntity))) {
                    // Keep rule, but mark it as unusable
                    this.unusableInstances.add(new Pair<TyClassEntity, TyConsEntity>(
                        (TyClassEntity) cc.getTyClass().getEntity(), tyConsEntity));

                    /*
                    it.remove();
                    */
                }
            }
        }
        if (entities.contains(this.num)) {
            this.num = null;
        }
        //HaskellSym.showee(this);
    }

    /**
     * keeps only constraints which are covered by the matrix it keeps only the constraints which contains only
     * variables wchih also occur in the matrix example: the call matrixReduce( (Bounded a,Eq a,Ord b),List a) returns
     * (Bounded a,Eq a) Ord b is not covered cause b does not occur in the matrix List a
     */
    public Set<ClassConstraint> matrixReduce(final Set<ClassConstraint> ccs, final HaskellType matrix) {
        final Set<ClassConstraint> res = new HashSet<ClassConstraint>();
        final Set<HaskellSym> syms = new HashSet<HaskellSym>();
        final Set<HaskellSym> fsyms = new HashSet<HaskellSym>();
        final FreeVarSymCollector fvsc = new FreeVarSymCollector(syms);
        matrix.visit(fvsc);
        final FreeVarSymCollector ccfvsc = new FreeVarSymCollector(fsyms);
        for (final ClassConstraint cc : ccs) {
            fsyms.clear();
            cc.visit(ccfvsc);
            if (syms.containsAll(fsyms)) {
                res.add(cc);
            }
        }
        return res;
    }

}
