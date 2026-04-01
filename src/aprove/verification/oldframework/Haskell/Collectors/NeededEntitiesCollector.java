package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This Visitor collect the group in each entity frame,
 * the top entities of all modules are in one major entity frame.
 * Eeach entity frame is splitted into mutual recusive blocks (groups), these are
 * saved in the HaskellObject carrying the entity frame.
 */
public class NeededEntitiesCollector extends HaskellVisitor {

    // already known
    public Map<HaskellEntity,Map<InstEntity,VarEntity>> instanceMap;
    public Map<TyClassEntity,Map<TyConsEntity,InstEntity>> clCoInstMap;
    public Map<TyClassEntity,Set<InstEntity>> availableInstances;

    public VarEntity equalEntity;
    public VarEntity minusEntity;
    public VarEntity geqEntity;
    public VarEntity andEntity;
    public VarEntity errorEntity;
    public VarEntity termiEntity;
    public VarEntity fromIntEntity;
    public VarEntity fromDoubleEntity;

    public TyConsEntity boolEntity;
    public TyConsEntity intEntity;
    public TyConsEntity natEntity;
    public TyConsEntity charEntity;
    public Prelude prelude;
    public Assumptions assumptions;

    public Cons bool;
    public Cons tyCoInt;
    public Cons tyCoDouble;

    private static final int TYPE_METRIC_OFFSET = 5; // the type metric may rise this much above the initial type metric for every (C|I)Var
    private Map<HaskellEntity, Integer> civar2typemetric;
    private Set<HaskellEntity> civarMetricExceeded;

    public Queue<Call> calls;
    public Set<Call> callsDone;
    public Collection<CVarEntity> entityValuesNotNeeded;
    public Set<HaskellEntity> entitiesDone;

    // Visitor relevant
    public HaskellSubstitution instantiation;
    boolean pat; // true, if we are in a pattern

    boolean hasAnd;

    private boolean inInitialization;

    private Cons getBoolCons() {
        if (this.bool == null) {
            this.bool = new Cons(new HaskellNamedSym(this.prelude.getBool()));
        }
        return this.bool;
    }


    private Cons getIntCons() {
        if (this.tyCoInt == null) {
            this.tyCoInt = new Cons(new HaskellNamedSym(this.prelude.getEntity(this,"Prelude","Int",HaskellEntity.Sort.TYCONS)));
        }
        return this.tyCoInt;
    }

    private Cons getDoubleCons() {
        if (this.tyCoDouble == null) {
            this.tyCoDouble = new Cons(new HaskellNamedSym(this.prelude.getEntity(this,"Prelude","Double",HaskellEntity.Sort.TYCONS)));
        }
        return this.tyCoDouble;
    }

    public NeededEntitiesCollector(Prelude prelude,Assumptions assumptions){
        this.assumptions = assumptions;
        this.prelude = prelude;
        this.boolEntity  = (TyConsEntity)this.prelude.getBool();
        this.intEntity   = (TyConsEntity)this.getTyEntity("Int");
        this.natEntity   = (TyConsEntity)this.getTyEntity("Nat");
        this.charEntity  = (TyConsEntity)this.getTyEntity("Char");
        this.equalEntity = this.getEntity("==");
        this.minusEntity = this.getEntity("-");
        this.geqEntity   = this.getEntity(">=");
        this.andEntity   = this.getEntity("&&");
        this.fromIntEntity   = this.getEntity("fromInt");
        this.fromDoubleEntity   = this.getEntity("fromDouble");

        this.pat = false;

        this.bool = null;
        this.tyCoInt = null;
        this.tyCoDouble = null;

        this.entitiesDone = new HashSet<HaskellEntity>();
        this.entityValuesNotNeeded = new HashSet<CVarEntity>();
        this.callsDone = new HashSet<Call>();
        this.calls = new LinkedList<Call>();

        this.civar2typemetric = new HashMap<HaskellEntity, Integer>();
    }

    @Override
    public void fcaseLambdaExp(LambdaExp ho){
        this.pat = true;
    }

    @Override
    public void icaseLambdaExp(LambdaExp ho){
        this.pat = false;
    }

    @Override
    public void fcaseAltExp(AltExp ho){
        this.pat = true;
    }

    @Override
    public void icaseAltExp(AltExp ho){
        this.pat = false;
    }

    @Override
    public void fcaseHaskellRule(HaskellRule ho){
        this.pat = true;
    }

    @Override
    public void icaseHaskellRule(HaskellRule ho){
        this.pat = false;
    }

    private void checkAndEntity(){
        if (!this.hasAnd) {
            this.addCall(this.andEntity,this.buildParam(Copy.deep(this.getBoolCons()),Copy.deep(this.getBoolCons())));
            this.entitySwitch(this.boolEntity);
            this.hasAnd = true;
        }
    }

    private void eqPatCheck(HaskellObject ho){
        if (this.pat) {
            this.addCall(this.equalEntity,this.buildParam(ho.getTypeTerm(),Copy.deep(this.getBoolCons())));
            this.checkAndEntity();
        }
    }


    @Override
    public HaskellObject casePlusPat(PlusPat ho) {
        this.entitySwitch(this.intEntity);
        this.entitySwitch(this.natEntity);
        this.addCall(this.geqEntity,this.buildParam(ho.getTypeTerm(),Copy.deep(this.getBoolCons())));
        this.addCall(this.minusEntity,this.buildParam(ho.getTypeTerm(),Copy.deep(ho.getTypeTerm())));
        this.checkAndEntity();
        return ho;
    }

    @Override
    public HaskellObject caseIntegerLit(IntegerLit ho) {
        this.entitySwitch(this.intEntity);
        this.entitySwitch(this.natEntity);
        this.addCall(this.fromIntEntity,this.prelude.buildArrow(Copy.deep(this.getIntCons()),Copy.deep(ho.getTypeTerm())));
        this.eqPatCheck(ho);
        return ho;
    }

    @Override
    public HaskellObject caseFloatLit(FloatLit ho) {
        this.entitySwitch(this.intEntity);
        this.entitySwitch(this.natEntity);
        this.addCall(this.fromDoubleEntity,this.prelude.buildArrow(Copy.deep(this.getDoubleCons()),Copy.deep(ho.getTypeTerm())));
        this.eqPatCheck(ho);
        return ho;
    }

    @Override
    public HaskellObject caseCharLit(CharLit ho) {
        this.entitySwitch(this.charEntity);
        //entitySwitch(this.intEntity);
        this.entitySwitch(this.natEntity);
        this.eqPatCheck(ho);
        return ho;
    }

    @Override
    public void fcaseAll(HaskellObject ho) {
        if (ho.getTypeTerm() != null) {
            ho.getTypeTerm().visit(this);
        }
    }

    @Override
    public void fcaseVar(Var ho) {
        if (this.instantiation!= null && !this.pat){
           if (ho.getSymbol() != null){
               VarEntity ve = (VarEntity)ho.getSymbol().getEntity();
               if ( (ve != null) && (!(ve instanceof TyVarEntity)) ) {
                   if (!ve.getLocal()) {
                       this.addCall(ve,(HaskellType)this.instantiation.applyTo(ho.getTypeTerm()));
                   }
               }
           }
        }
    }


    @Override
    public boolean guardEntity(HaskellEntity ho) {
        this.entitySwitch(ho);
        return false;
    }


    private void entitySwitch(Set<HaskellEntity> hos) {
        for (HaskellEntity ho : hos){
            this.entitySwitch(ho);
        }
    }

    private void entitySwitch(HaskellEntity ho) {
        if (!this.entitiesDone.contains(ho)){
            this.entitiesDone.add(ho);
            HaskellSubstitution oldinst = this.instantiation;
            this.instantiation = null;
            switch (ho.getSort()) {
            case TYCONS:
                this.entitySwitch(ho.getSubEntities());
                break;

            case CONS:
                // visit the TypeSchema of this constructor
                ho.getType().visit(this);
                break;

            case INST:
                InstEntity ie = (InstEntity) ho;
                this.entitySwitch(ie.getTyClassEntity());
                this.entitySwitch(ie.getTyConsEntity());
                break;

            case VAR:
                if (ho instanceof CVarEntity) {
                    CVarEntity cve = (CVarEntity) ho;
                    this.entitySwitch(cve.getParentEntity());
                    this.assumptions.getTypeSchemaFor(ho).visit(this);
                } else {
                    VarEntity ve = (VarEntity) ho;
                    if (!ve.getLocal()) {
                        this.assumptions.getTypeSchemaFor(ho).visit(this);
                        ve.getValue().visit(this);
                    }
                }
                break;

            case IVAR:
                IVarEntity ive = (IVarEntity) ho;
                this.entitySwitch(ive.getParentEntity());
                break;

            case TYCLASS:
                Set<ClassConstraintRule> ccrules = this.prelude.getModules().getCcg().getRulesForClass((TyClassEntity) ho);
                if (ccrules != null) {
                    for (ClassConstraintRule ccr : ccrules) {
                        ClassConstraint cc = ccr.getPattern();
                        TyClassEntity instClassEntity = (TyClassEntity) cc.getTyClass().getEntity();
                        TyConsEntity  instConsEntity  = (TyConsEntity)  ((Atom)HaskellTools.getLeftMost(cc.getType())).getSymbol().getEntity();

                        // add the InstEntity for this Class Constraint Rule (during initialization, it is okay to skip this)
                        Map<TyConsEntity, InstEntity> tyCons2InstEntities = this.clCoInstMap.get(instClassEntity);
                        if ( (aprove.Globals.useAssertions) && (!this.inInitialization) ) {
                            assert(tyCons2InstEntities != null) : "An instance for an unknown class was used";
                        }

                        if (tyCons2InstEntities != null) {
                            InstEntity ruleInstEntity = tyCons2InstEntities.get(instConsEntity);
                            if (aprove.Globals.useAssertions) {
                                assert (ruleInstEntity != null) : "An instance rule without an InstEntity was used";
                            }
                            ruleInstEntity.visit(this);
                        }

                        ccr.visit(this);
                    }
                }
            }

            this.instantiation = oldinst;
        }
    }


    /**
     * counts the number of constructors and variables in the type, helper for
     * checkCall()
     *
     * @param type
     *            The type to count the constructors for
     * @return the numer of constructors and variables in the given type
     */
    @SuppressWarnings("unchecked") // since only the size of tmpList is
                                    // necessary, there is no need for a second
                                    // list...
    private static int typeMetric(HaskellType type) {
        List tmpList = new ArrayList();
        // it is absolutely necessary that a List is used, since duplicate types _must_ be considered.
        // Therefore, ConsSymCollector.applyTo() is not applicable, as this uses a Set.
        ConsSymCollector csc = new ConsSymCollector(tmpList);
        type.visit(csc);
        csc = null;
        int conss = tmpList.size();

        tmpList.clear();
        FreeLocalVarCollector flvc = new FreeLocalVarCollector(tmpList);
        type.visit(flvc);

        return conss + tmpList.size();
    }

    /**
     * Checks whether this is a call to an InstEntity, or a CVarEntity
     * which weakly reduces types according to some metric.
     * If it is found, that the types increase over the initial bounds plus some offset,
     * all instances are added to the set of needed instances. No changes are made to this.changed.
     * @param call The call to check
     * @return whether the call made the change necessary (i.e. outside must set this.changed to true)
     */
    private boolean checkCIVarCall(Call call) {
        HaskellEntity he = call.getKey();
        if ( (he instanceof IVarEntity) || (he instanceof CVarEntity) ) {

            if (this.civarMetricExceeded != null) {
                if (this.civarMetricExceeded.contains(he)) {
                    return true; // already all instances were added for this CIVar, thus no following needed
                }
            }

            Integer initTypeMetric = this.civar2typemetric.get(he);
            if (initTypeMetric == null) {
                initTypeMetric = NeededEntitiesCollector.typeMetric(call.getValue());
                this.civar2typemetric.put(he, initTypeMetric);
                return false; // this call was the initial call to this IVar
            }

            // there already was a call to this CIVar... check for weak type decrease
            int curMetric = NeededEntitiesCollector.typeMetric(call.getValue());
            if (curMetric <= initTypeMetric+NeededEntitiesCollector.TYPE_METRIC_OFFSET) {
                return false; // we are still in bounds, so follow...
            }

            // we have left the allowed range of types => Add all instances for this class
            CVarEntity cve;
            if (he instanceof IVarEntity) {
                IVarEntity ive = (IVarEntity) he;
                cve = (CVarEntity) ((InstFunction)ive.getValue()).getMemberForInst();
            }
            else /* if (he instanceof CVarEntity) */ {
                cve = (CVarEntity) he;
            }

            // add calls for every instance of the current class
            MemberTypeSchema mts = (MemberTypeSchema) cve.getType();
            this.addCallsForAllInstances(cve, mts.getMatrix(), mts.getClassConstraint().getType());


            // mark this CIVar, as all instances were added and no checks are needed for it anymore
            if (this.civarMetricExceeded == null) {
                this.civarMetricExceeded = new HashSet<HaskellEntity>();
            }
            this.civarMetricExceeded.add(he);

            return true; // add all the instances of the above created Call for the next round, but do nothing for the current call
        }

        return false; // for everything else, we need to follow this call
    }

    private HaskellType buildParam(HaskellType parType,HaskellType res){
        return this.prelude.buildArrow(Copy.deep(parType),this.prelude.buildArrow(parType,res));
    }


    private void addCall(VarEntity ve) {
        TypeSchema ts = this.assumptions.getTypeSchemaFor(ve);
        HaskellType ht = ts.getMatrix();

        this.addCall(ve,ht);
    }

    public void addCall(VarEntity ve,HaskellType t){
        if (ve instanceof CVarEntity){
            TyClassEntity tcle = (TyClassEntity) ve.getParentEntity();
            MemberTypeSchema mts = Copy.deep((MemberTypeSchema) ve.getType());
            HaskellSubstitution subs = BasicTerm.Tools.mgu(t,mts.getMatrix());
            t = (HaskellType)subs.applyToDestructive(t);
            HaskellType instance = (HaskellType) subs.applyToDestructive(mts.getClassConstraint().getType());
            Atom atom = (Atom) HaskellTools.getLeftMost(instance);
            if (atom.getBasicSort() == BasicTerm.Sort.CONS){
                TyConsEntity tcoe = (TyConsEntity) atom.getSymbol().getEntity();

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("clCo: "+tcle+"  "+tcoe);
                }

                InstEntity ie = this.clCoInstMap.get(tcle).get(tcoe);
                if (ie == null){
                    HaskellSym.showee(new Apply(tcle,tcoe));
                }
                this.addCallForInstance(ve,ie,t);
            } else {
                this.addCallsForAllInstances((CVarEntity) ve, t, instance);
            }

        }  else {
            this.addCall(new Call(ve,t));
        }
    }


    public void addCall(Call call){
        if (!this.callsDone.contains(call)) {
            if (this.calls.add(call)) {
            }
        }
    }

    private boolean checkVarBigType(Call call){
        VarEntity he = call.getKey();
        Integer initTypeMetric = this.civar2typemetric.get(he);
        if (initTypeMetric == null) {
            initTypeMetric = NeededEntitiesCollector.typeMetric(call.getValue());
            this.civar2typemetric.put(he, initTypeMetric);
            return false; // this call was the initial call to this Var
        }
        if (NeededEntitiesCollector.typeMetric(call.getValue()) <= initTypeMetric+NeededEntitiesCollector.TYPE_METRIC_OFFSET) {
            return false;
        }
        HaskellSubstitution subs = this.instantiation;
        this.instantiation = new HaskellSubstitution();
        he.getValue().visit(this);
        this.instantiation = subs;
        return true;
    }

    public void makeCall(Call call){
        if (!this.checkCIVarCall(call) && !this.checkVarBigType(call)){
            VarEntity ve = call.getKey();
            TypeSchema ts = this.assumptions.getTypeSchemaFor(call.getKey());
            HaskellType freshInst = (HaskellType)(Copy.deep(call.getValue()).visit(new FreshVars()));
            this.instantiation = BasicTerm.Tools.mgu(Copy.deep(ts.getMatrix()),freshInst);
            if (this.instantiation == null) {
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    System.out.println("E:"+call.getKey());
                    System.out.println("A:"+ts.getMatrix());
                    System.out.println("B:"+call.getValue());
                }

                HaskellSym.showee(call.getValue());
                HaskellError.output(call.getKey(), "Instantiation could not be built.");
            }
            ve.getValue().visit(this);
        }
    }

    public void addCallForInstance(VarEntity e,InstEntity ie,HaskellType t){
        VarEntity ve = this.instanceMap.get(e).get(ie);
        if (ve == null) {
            ve = e;
            this.entityValuesNotNeeded.remove(e);
        } else {
            this.entitySwitch(ve);
        }
        this.addCall(new Call(ve,t));
    }

    public HaskellType buildFreshInstance(InstEntity ie){
       HaskellType t = Copy.deep(ie.getInstTypeTerm());
       return (HaskellType) t.visit(new FreshVars());
    }

    /**
     * Adds a call for every IVar of the current CVar that is passed
     * @param e The current Class member function
     * @param t the current type (i.e. the type that is most special)
     * @param instance the type the class member variable is currently specialized with (MUST start with a variable)
     */
    private void addCallsForAllInstances(CVarEntity e, HaskellType t, HaskellType instance) {
        TyClassEntity tcle = (TyClassEntity) e.getParentEntity();
        Atom atom = (Atom) HaskellTools.getLeftMost(instance);
        Var tyVar = (Var) atom;
        Set<InstEntity> ies = this.availableInstances.get(tcle);
        for (InstEntity ie : ies){
            HaskellType z = this.buildFreshInstance(ie);
            HaskellSubstitution curInst = BasicTerm.Tools.mgu(Copy.deep(instance),z);
            if (curInst != null) {
                this.addCallForInstance(e,ie,(HaskellType)curInst.applyTo(t));
            }
        }
    }


    /**
     * <b>must not</b> be called with names that are not predefined
     */
    private VarEntity getEntity(String name){
        if (this.prelude.isSimplePrelude()) {
            return (VarEntity)this.prelude.getEntityN(this,"Prelude",name,HaskellEntity.Sort.VAR);
        }

        return (VarEntity)this.prelude.getEntity(this,"Prelude",name,HaskellEntity.Sort.VAR);
    }


    /**
     * <b>must not</b> be called with names that are not predefined
     */
    private HaskellEntity getTyEntity(String name){
        if (this.prelude.isSimplePrelude()) {
            return this.prelude.getEntityN(this,"Prelude",name,HaskellEntity.Sort.TYCONS);
        }

        return this.prelude.getEntity(this,"Prelude",name,HaskellEntity.Sort.TYCONS);
    }

    public Set<HaskellEntity> getUnreachables(Modules modules,Collection<Pair<HaskellObject,HaskellExp>> startTerms){
        Set<HaskellEntity> unreachables = new HashSet<HaskellEntity>();

        this.bool = new Cons(new HaskellNamedSym(this.prelude.getBool()));

        this.hasAnd = false;
        this.inInitialization = true;

        Collection<Call> startCalls = new HashSet<Call>();
        this.instanceMap = new HashMap<HaskellEntity,Map<InstEntity,VarEntity>>();
        this.clCoInstMap = new HashMap<TyClassEntity,Map<TyConsEntity,InstEntity>>();
        this.availableInstances = new HashMap<TyClassEntity,Set<InstEntity>>();
        this.entitySwitch(this.getEntity("error"));
        this.entitySwitch(this.getEntity("errorFrame"));
        this.entitySwitch(this.getEntity("terminator"));

        this.entitySwitch(this.boolEntity);
        this.entitySwitch(this.prelude.getEntity(this,"Prelude","[]",HaskellEntity.Sort.TYCONS));


        if (!this.prelude.isSimplePrelude()) {
            this.tyCoInt = new Cons(new HaskellNamedSym(this.prelude.getEntity(this,"Prelude","Int",HaskellEntity.Sort.TYCONS)));
            this.tyCoDouble = new Cons(new HaskellNamedSym(this.prelude.getEntity(this,"Prelude","Double",HaskellEntity.Sort.TYCONS)));

            // FIXME this should only be added in case of lazy termination checking
            this.entitySwitch((TyClassEntity)this.prelude.getEntity(null, "", "LazyTermination", HaskellEntity.Sort.TYCLASS));
            this.entitySwitch((VarEntity)this.prelude.getEntity(null, "", "lazyTerminating", HaskellEntity.Sort.VAR));
            this.entitySwitch((VarEntity)this.prelude.getEntity(null, "", "lazyGenerator", HaskellEntity.Sort.VAR));
            this.entitySwitch(this.natEntity);

            this.addCall((VarEntity)this.andEntity);
            InstEntity lazyApplyInst = (InstEntity)this.prelude.getEntity(null, "", "LazyTermination$->", HaskellEntity.Sort.INST);
            this.entitySwitch(lazyApplyInst);
            for(HaskellEntity ve : lazyApplyInst.getSubEntities()) {
                this.addCall((VarEntity) ve);
            }
            this.addCall((VarEntity)this.prelude.getEntity(null, "", "seq", HaskellEntity.Sort.VAR));
            this.addCall((VarEntity)this.prelude.getEntity(null, "", "enforceWHNF", HaskellEntity.Sort.VAR));
            this.entitySwitch((TyConsEntity)this.prelude.getEntity(null, "", "WHNF", HaskellEntity.Sort.TYCONS));
        }

        //this.neededVars.add(this.getEntity("fromInt"));
        for (Module m : modules.getModules()){
            for (HaskellEntity e : m.getCollectedEntities()){
                if ((e.getSort() == HaskellEntity.Sort.INST)){
                    unreachables.add(e);
                    InstEntity ie = (InstEntity) e;

                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        System.out.println("Found:"+ie);
                    }

                    TyConsEntity tcoe = (TyConsEntity) ie.getTyConsEntity();
                    TyClassEntity tcle = (TyClassEntity) ie.getTyClassEntity();
                    Set<InstEntity> instances = this.availableInstances.get(tcle);
                    if (instances == null){
                        instances = new HashSet<InstEntity>();
                        this.availableInstances.put(tcle,instances);
                    }

                    instances.add(ie);
                    Map<TyConsEntity,InstEntity> coiMap = this.clCoInstMap.get(tcle);
                    if (coiMap == null) {
                        coiMap = new HashMap<TyConsEntity,InstEntity>();
                        this.clCoInstMap.put(tcle,coiMap);
                    }
                    coiMap.put(tcoe,ie);

                    for (HaskellEntity ive : e.getSubEntities()){
                         InstFunction instfunc = (InstFunction) ive.getValue();
                         HaskellEntity cve = instfunc.getMemberForInst();
                         Map<InstEntity,VarEntity> memberIMap = this.instanceMap.get(cve);
                         if (memberIMap == null) {
                             memberIMap = new HashMap<InstEntity,VarEntity>();
                             this.instanceMap.put(cve,memberIMap);
                         }
                         memberIMap.put(ie,(VarEntity) ive);

                    }
                } else  if ((e.getSort() == HaskellEntity.Sort.TYCLASS)){
                    TyClassEntity tcle = (TyClassEntity) e;
                    Set<InstEntity> instances = this.availableInstances.get(tcle);
                    if (instances == null){
                        instances = new HashSet<InstEntity>();
                        this.availableInstances.put(tcle,instances);
                    }
                    unreachables.add(e);
                    if (this.clCoInstMap.get(e) == null){
                        this.clCoInstMap.put(tcle,new HashMap<TyConsEntity,InstEntity>());
                    }
                    for (HaskellEntity cve : e.getSubEntities()){
                        this.entityValuesNotNeeded.add((CVarEntity)cve);
                        if (this.instanceMap.get(cve) == null){
                            this.instanceMap.put(cve,new HashMap<InstEntity,VarEntity>());
                        }
                    }
                } else  if (e.getSort() == HaskellEntity.Sort.IVAR) {
                    unreachables.add(e);
                }  else  if (e.getSort() == HaskellEntity.Sort.CONS) {
                    unreachables.add(e);
                } else  if (e.getSort() == HaskellEntity.Sort.TYCONS) {
                    unreachables.add(e);
                } else  if (e.getSort() == HaskellEntity.Sort.VAR) {
                    unreachables.add(e);
                    if (startTerms.size()==0) {
                        if (!(e instanceof CVarEntity)) {
                            if (m.isMainModule()){
                                // all non-CVars shall be analyzed for termination...
                                startCalls.add(new Call((VarEntity)e,null));
                            }
                        }
                    }
                }
            }
        }

        this.inInitialization = false;


        if (startTerms.size() > 0) {
            startCalls.clear();
            for (Pair<HaskellObject,HaskellExp> typedTerm : startTerms){
                this.instantiation = new HaskellSubstitution();
                TypeSchema ts = (TypeSchema)typedTerm.getKey();
                for (ClassConstraint cc : ts.getConstraints()){
                    cc.visit(this);
                }
                typedTerm.getValue().visit(this);
            }
        }

        while (!this.calls.isEmpty()){
            Call call = this.calls.remove();
            this.callsDone.add(call);
            this.makeCall(call);
        }

        for (CVarEntity cve : this.entityValuesNotNeeded){
            cve.setValue(null);
        }
        unreachables.removeAll(this.entitiesDone);
        return unreachables;
    }

    @Override
    public boolean guardDefType(SynTypeDecl ho)        { return false;}
    @Override
    public boolean guardDataType(DataDecl ho)          { return false;}
    @Override
    public boolean guardConss(DataDecl ho)             { return false;}
    @Override
    public boolean guardEntities(Module ho)            { return false;}
    @Override
    public boolean guardValue(HaskellEntity ho)        { return true;}
    @Override
    public boolean guardType(HaskellEntity ho)         { return false;}
    @Override
    public boolean guardMember(HaskellEntity ho)       { return false;}
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
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) { return true;}
    @Override
    public boolean guardDerivings(DataDecl ho)         {  return false; }

    public static class Call extends Pair<VarEntity,HaskellType>{
        public Call(VarEntity e,HaskellType t){
            super(e,t);
        }

        @Override
        public boolean equals(Object obj){
            Call call = (Call) obj;
            if (call.getKey() != this.getKey()) {
                return false;
            }
            if (this.getValue() == call.getValue()) {
                return true;
            }
            if (this.getValue() == null) {
                return false;
            }
            if  (call.getValue() == null) {
                return false;
            }
            return BasicTerm.Tools.equalsModuloVariables(this.getValue(),call.getValue());
        }

        @Override
        public int hashCode(){
            return this.getKey().hashCode();
        }
    }


    public static class FreshVars extends HaskellVisitor{
        @Override
        public HaskellObject caseVar(Var var){
            return new Var(new HaskellSym());
        }
    }

}
