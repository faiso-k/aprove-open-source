package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Haskell.Visitors.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The Modules represents a whole Haskell program.
 */
public class Modules extends HaskellObject.Visitable implements HaskellBean {
    protected static Logger log = Logger.getLogger("aprove.verification.oldframework.Haskell");


    Set<String> alreadyLoadedModulesNames;
    Set<Module> alreadyLoadedModules;
    Prelude prelude;
    List<Group> groups;
    Map<String,Module> modMap; // map from module name to module
    Set<String> neededModules;
    List<Pair<HaskellObject,HaskellExp>> startTerms;

    String nextNeededModule;
    String name;
    Module mainModule;

    boolean fullCopy;  // if true the buffers are copied too by Deepcopy

    // Buffer
    Set<HaskellBasicRule> typeRules;  // type synonym rules
    Assumptions assumptions;          // type assumptions of all modules togheter
    EntityAssumptions kindAssumptions; // kind assumptions of all modules togheter
    ClassConstraintGraph ccg;   // the ClassConstraintGraph contains the class hierachy

    // no deepcopy for the following members, only for caching and PreludeSer.hs
    Set<HaskellEntity> unreachables;

    public boolean getFullCopy(){
        return this.fullCopy;
    }

    public void setFullCopy(boolean fullCopy){
        this.fullCopy = fullCopy;
    }

    public void setAssumptions(Assumptions assumptions){
        this.assumptions = assumptions;
    }

    public Assumptions getAssumptions(){
        return this.assumptions;
    }

    /**
     * constructor used by the parser
     */
    public static synchronized Modules createModules(Modules preModules){
        for(Module m : preModules.getModules()) {
            m.setAlreadyLoaded(false);
        }
        preModules.prelude.setAccessible(true);
        HaskellEntity.HaskellEntitySkeleton.count = 200000;
        Modules.log.log(Level.INFO,"Add Prelude to moduleset\n");
        Modules cPreModules = Copy.deep(preModules);
        cPreModules.prelude.setAccessible(false);
        cPreModules.alreadyLoadedModulesNames = new HashSet<String>();
        cPreModules.alreadyLoadedModules = new HashSet<Module>();
        for(Module m : cPreModules.getModules()) {
            m.setAlreadyLoaded(true);
            cPreModules.alreadyLoadedModulesNames.add(m.getName());
            cPreModules.alreadyLoadedModules.add(m);
        }
        for(Module m : preModules.getModules()) {
            m.setAlreadyLoaded(true);
        }
        return cPreModules;
    }

    public Modules(){
        this.prelude = null;
        this.alreadyLoadedModulesNames = null;
        this.alreadyLoadedModules = null;
        this.modMap = new HashMap<String,Module>();
        this.neededModules = new HashSet<String>();
        this.nextNeededModule = null;
        this.name = null;
        this.groups = null;
        this.mainModule = null;
        this.startTerms = new Vector<Pair<HaskellObject,HaskellExp>>();
        this.typeRules = null;
        this.assumptions = null;
        this.kindAssumptions = null;
        this.ccg = null;
        this.fullCopy = false;
    }

    @Override
    public HaskellObject deepcopy(){
        Modules newModules = new Modules();
        List<HaskellEntity> newEntities = new Vector<HaskellEntity>();
        List<EntityFrame> newEntityFrames = new Vector<EntityFrame>();
        Map<HaskellObject,HaskellObject> repMap = new HashMap<HaskellObject,HaskellObject>();
        newModules.startTerms = new Vector<Pair<HaskellObject,HaskellExp>>();
        for (Pair<HaskellObject,HaskellExp> st : this.startTerms){
             newModules.startTerms.add(new Pair<HaskellObject,HaskellExp>(Copy.deep(st.getKey()),Copy.deep(st.getValue())));
        }
        if (this.fullCopy) {
            newModules.typeRules = Copy.deepCol(this.typeRules);
            newModules.kindAssumptions = Copy.deep(this.kindAssumptions);
        }
        newModules.assumptions = Copy.deep(this.assumptions);

        PreCopyVisitor preCV = new PreCopyVisitor(repMap,newEntities,newEntityFrames,newModules);
        this.visit(preCV);

        PostCopyVisitor postCV = new PostCopyVisitor(repMap);
        for(EntityFrame ef : newEntityFrames){
            if (ef.getCollectedEntities().size()>0) {
                postCV.entityFrameVisit(ef);
            } else {
                postCV.entityFrameVisit(ef);
            }
        }
        for(HaskellEntity e : newEntities){
            postCV.entityVisit(e);
        }
        postCV.normalVisit(newModules);

        //if (this.fullCopy){
            if (this.ccg != null) {
               newModules.ccg = this.ccg.entityCopy(repMap);
               newModules.ccg.visit(postCV);
            } else {
               newModules.ccg = null;
            }
        //}


            PostPostCopyVisitor ppcv = new PostPostCopyVisitor(true,repMap,newEntities,newEntityFrames,newModules);
            newModules.visit(ppcv);
            newModules.getCcg().visit(ppcv);

        //this.visit(new PostPostCopyVisitor(false,repMap,newEntities,newEntityFrames,newModules));
        Modules res = (Modules) this.hoCopy(newModules);
        return res;
    }

    /**
     * @returns a set of entities which names are not unique in whole haskellprogram
     */
    public Set<HaskellEntity> buildNotUniqueGroup(){
        Set<HaskellEntity> notUnique = new HashSet<HaskellEntity>();
        EntityMap name2entity = new EntityMap();
        for (Module m : this.getModules()){
            for(HaskellEntity e : m.getLocalEntities()){
                if (!(e instanceof IVarEntity)) {
                    HaskellEntity found = name2entity.get(e.getName(),e.getSort());
                    if (found != null) {
                       notUnique.add(e);
                       notUnique.add(found);
                    } else {
                       name2entity.add(e);
                    }
                }
            }
        }
        return notUnique;
    }

    public ClassConstraintGraph getClassConstraintGraph(){
        return this.ccg;
    }

    public void setCcg(ClassConstraintGraph ccg){
        this.ccg = ccg;
    }

    public ClassConstraintGraph getCcg(){
        return this.ccg;
    }

    public List<Group> getGroups(){
        return this.groups;
    }

    public void setGroups(List<Group> groups){
        this.groups = groups;
    }

    public String getName(){
        return this.name;
    }

    public void setName(String name){
        this.name = name;
    }


    private void buildAlreadyLoadedModulesAndNames() {
        this.alreadyLoadedModulesNames = new HashSet<String>();
        this.alreadyLoadedModules = new HashSet<Module>();
        for(Module m : this.getModules()) {
            if (m.isAlreadyLoaded()) {
                this.alreadyLoadedModulesNames.add(m.getName());
                this.alreadyLoadedModules.add(m);
            }
        }
    }

    /**
     * @return the modules that were already loaded in the serialized modules
     */
    public Set<Module> getAlreadyLoadedModules() {
        if (this.alreadyLoadedModules == null) {
            this.buildAlreadyLoadedModulesAndNames();
        }
        return this.alreadyLoadedModules;
    }

    /**
     * @return the names of the modules that were already loaded in the serialized modules
     */
    public Set<String> getAlreadyLoadedModulesNames() {
        if (this.alreadyLoadedModulesNames == null) {
            this.buildAlreadyLoadedModulesAndNames();
        }
        return this.alreadyLoadedModulesNames;
    }

    public Prelude getPrelude(){
        return this.prelude;
    }

    public void setPrelude(Prelude prelude){
        this.prelude = prelude;
    }

    public Module getMainModule(){
        return this.mainModule;
    }

    public void setMainModule(Module mainModule){
        this.mainModule = mainModule;
    }

    public Map<String,Module> getModMap(){
        return this.modMap;
    }

    public void setModMap(Map<String,Module> modMap){
        this.modMap = modMap;
    }

    public void addNeededModule(String name){
        this.neededModules.add(name);
    }

    public void addModule(Module m){
        if (m.isMainModule()){
            this.name = m.getName();
            this.mainModule = m;

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("mainFound");
            }
        }
        this.modMap.put(m.getName(),m);
        m.setModules(this);
    }

    /**
     * adds a module to this modules
     * and build the import map for the given module
     */
    public void addModuleAndBuildImpMap(Module m){
        this.addModule(m);
        m.buildImpMap();
    }

    /**
     * @returns all entities which are exported by one module with the given qualifier as name
     */
    public Set<HaskellEntity> getExportEntitiesFor(String qual){
        return this.modMap.get(qual).getExportEntities();
    }

    /**
     * @returns a set of the Names of needed modules
     */
    public Set<String> getNamesOfNeededModules(){
        Set<String> names = new HashSet<String>(this.neededModules);
        names.removeAll(this.modMap.keySet());
        return names;
    }

    /**
     * @return true,iff some module needed to be loaded
     */
    public boolean needMoreModules(){
        Set<String> names = new HashSet<String>(this.neededModules);
        names.removeAll(this.modMap.keySet());
        if (names.size()>0) {
           this.nextNeededModule = names.iterator().next();
           return true;
        } else {
           this.nextNeededModule = null;
           return false;
        }
    }

    /**
     * @returns the next module to be loaded
     */
    public String getNextNeededModule(){
        return this.nextNeededModule;
    }

    public void setNextNeededModule(String nextNeededModule){
        this.nextNeededModule = nextNeededModule;
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        for (Module m : this.modMap.values()){
            if (m.isAccessible()){
                m.visit(hv);
            }
        }
        if (hv.guardStartTerms(this)){
            hv.fcaseStartTerms(this);
            for (Pair<HaskellObject,HaskellExp> st : this.startTerms){
                st.setKey(this.walk(st.getKey(),hv));
                st.setValue(this.walk(st.getValue(),hv));
            }
            hv.icaseStartTerms(this);
        }
        if (hv.guardTypeRules(this)){
            this.typeRules = this.listWalk(this.typeRules,hv);
        }
        if (hv.guardAssumptions(this)){
            this.assumptions = this.walk(this.assumptions,hv);
            this.kindAssumptions = this.walk(this.kindAssumptions,hv);
        }
        return this;
    }

    /**
     * @returns a set of all modules
     */
    public Set<Module> getModules(){
        return new HashSet(this.modMap.values());
    }

    public void collectEntities(){
        Modules.log.log(Level.INFO,"Collect all defined entities\n");
        HaskellVisitor hv = new CollectEntitiesVisitor();
        this.visit(hv);
        HaskellSym.show("After Collect",this);
    }

    /**
     * fixpoint iteration for exportlists of all modules.
     */
    public void buildExportLists(){
        boolean allEqual = false;
        Modules.log.log(Level.INFO,"Infer Exportlists of all modules\n");
        do {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Build:");
            }

            for (Module m : this.modMap.values()){
                Modules.log.log(Level.INFO,"Construct exportlists for "+m.getName()+"\n");

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    System.out.println("   buildexp: "+m.getName());
                }

                if (m.isAccessible()) {
                    m.buildExportEntities();
                }
            }
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Checking:");
            }

            allEqual = true;
            for (Module m : this.modMap.values()){
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    System.out.println("   Check: "+m.getName());
                }

                if (m.isAccessible()) {
                    // TODO verify: is this the right call order?
                    //      Or wouldn't it be better to put setNewExportEntities() up front, so that a module could already set its export entities?
                    allEqual = allEqual && m.setNewExportEntities();
                }
            }
        } while (!allEqual);
        HaskellSym.show("ExportList",this);
    }

    /**
     * set the entity of each occuring HaskellSym
     * @return the type rules (i.e. the type synonym replacement rules)
     */
    public void setSymbolEntity(){
        Modules.log.log(Level.INFO,"Map names to entities\n");
        SetSymbolEntityVisitor ssev = new SetSymbolEntityVisitor(this.prelude.getPreDefEntities(),this.typeRules,this.mainModule);
        this.visit(ssev);
        HaskellSym.show("setSymbolEntity",this);
        //return ssev.getTypeRules();
    }

    /**
     * correct the PatLambdaExp's
     */
    public void reducePatLambdaExps(){
        Modules.log.log(Level.INFO,"Translate Pattern Declaration ");
        PatLambdaExpVisitor plev = new PatLambdaExpVisitor();
        this.visit(plev);
        HaskellSym.show("PatLambdaExpVisitor",this);
        //return ssev.getTypeRules();
    }

    /**
     * @return a list of groups (sets of HaskellEntities)
     *         a group is a mutual recursive block of type declaration and class declaration
     *         which depend one each other.
     */
    public List<Set<HaskellEntity>> buildKindGroups(){
        Modules.log.log(Level.INFO,"Collect mutual recursive blocks for kind inference\n");
        KindDependencyVisitor kdv = new KindDependencyVisitor(this.prelude.getPreDefTyCons());
        this.visit(kdv);
        return kdv.buildGroups();
    }

    /**
     * @return all occuring type terms of all modules.
     */
    public Set<HaskellPreType> getInnerTypes(){
        CollectInnerTypesVisitor citv = new CollectInnerTypesVisitor();
        this.visit(citv);
        return citv.getInnerTypes();
    }

    /**
     * @return all occuring type terms of all modules.
     */
    public Set<HaskellPreType> getInnerTypes(HaskellObject ho){
        CollectInnerTypesVisitor citv = new CollectInnerTypesVisitor();
        ho.visit(citv);
        return citv.getInnerTypes();
    }

    /**
     * starts the kind inference over groups and innerTypes
     */
    public void kindInference(List<Set<HaskellEntity>> groups,Set<HaskellPreType> innerTypes){
        Modules.log.log(Level.INFO,"Kind inference\n");
        (new KindInferenceVisitor(this.kindAssumptions,this.prelude)).infer(groups,innerTypes);
        HaskellSym.show("Kind inference",this);
    }

    /**
     * transfroms all pre types to typeschema in all modules
     */
    public void preTypeToSchema(Set<HaskellBasicRule> rules){
        this.visit(new PreTypeToSchemaVisitor(rules));
        HaskellSym.show("Schemata",this);
    }

    /**
     * collects the class hierachy and class dependencies and store this in a Graph
     */
    public void collectClassConstraints(){
        HaskellVisitor hv = new ClassConstraintVisitor(this.ccg);
        this.visit(hv);
        this.ccg.checkAcyclic();
        //HaskellSym.showGraph(ccg);
        HaskellSym.show("Instantitation",hv);
    }

    /**
     * reduces the set of ClassConstraints to those that are covered by the type exp
     */
    public void reduceConstraintsBy(Set<ClassConstraint> ccs, HaskellType type){
        this.getClassConstraintGraph().reduce(ccs);
        Set<HaskellSym> varSyms = FreeVarSymCollector.applyTo(type);
        Iterator<ClassConstraint> it = ccs.iterator();
        while (it.hasNext()){
            Set<HaskellSym> cvs = FreeVarSymCollector.applyTo(it.next());
            // if a single type variable does not occur, remove ClassConstraint
            if (cvs.retainAll(varSyms)){
                it.remove();
            }
        }
    }

    /**
     * build all the typeschema instances for the instance entities.
     */
    public void instantiate(){
        HaskellVisitor hv = new InstantiationVisitor();
        this.visit(hv);
        HaskellSym.show("Instantitation",hv);
    }

    /**
     * starts type inference on the collected groups
     */
    public void typeInference(){
        Modules.log.log(Level.INFO,"Type inference\n");
        TypeInferenceVisitor tiv = (new TypeInferenceVisitor(this.prelude,this.assumptions,this.ccg));
        tiv.forModules(this);
    }

    /**
     * creates a DOM-Document that represent the whole Haskell program
     */
    public Document toDOM(){
        return XMLCreateVisitor.buildDOM(this,false,true,false);
    }

    public Document toFullDOM(){
        return XMLCreateVisitor.buildDOM(this,true,true,false);
    }

    public Document toBasicDOM(){
        /*ConsEntity ListCons = this.getPrelude().getListCons();
        ConsEntity ListNil = this.getPrelude().getListNil();
        TyConsEntity ListTy = this.getPrelude().getList();
        ListTy.setName("List");
        ListCons.setInfix(false);
        ListCons.setName("Cons");
        ListNil.setName("Nil");
        */
        return XMLCreateVisitor.buildDOM(this,true,false,true);
    }

    public void addStartTerm(Pair<HaskellObject,HaskellExp> typedTerm){
        this.startTerms.add(typedTerm);
    }

    public void removeStartTerm(Pair<HaskellObject,HaskellExp> typedTerm){
        this.startTerms.remove(typedTerm);
    }

    public List<Pair<HaskellObject,HaskellExp>> getStartTerms(){
        return this.startTerms;
    }

    public void setStartTerms(List<Pair<HaskellObject,HaskellExp>> startTerms){
        this.startTerms = startTerms;
    }

    /**
     * sets symbol entities of a start term in main module scope
     * @return TypeTerm of start term
     */
    public HaskellObject checkStartTerm(HaskellExp exp){
        if (this.ccg == null){
           return null;
        } else {
           CollectEntitiesVisitor cev = new CollectEntitiesVisitor();
           cev.fcaseModule(this.mainModule);
           exp.visit(cev);
           SetSymbolEntityVisitor ssev = new SetSymbolEntityVisitor(this.prelude.getPreDefEntities(),this.typeRules,this.mainModule);
           ssev.setModule(this.mainModule);
           exp.visit(ssev);
           exp.visit(new LabeledFieldTranslator(this.prelude));
           this.kindInference(new Vector<Set<HaskellEntity>>(),this.getInnerTypes(exp));
           exp.visit(new PreTypeToSchemaVisitor(this.typeRules));
           this.prelude.addDerivingsForTuplesAndBool();
           TypeInferenceVisitor tiv = (new TypeInferenceVisitor(this.prelude,this.assumptions,this.ccg));
           tiv.forTuples(this);

           TypeSchema ts = (TypeSchema) tiv.forTerm(exp,this.mainModule);

           return ts;
        }
    }

    /**
     * sets symbol entities of a start term in main module scope
     * @return TypeTerm of start term
     */
    public HaskellObject checkTerm(HaskellExp exp){
        if (this.ccg == null){
           return null;
        } else {
           TypeInferenceVisitor tiv = (new TypeInferenceVisitor(this.prelude,this.assumptions,this.ccg));
           return tiv.forTerm(exp,this.mainModule);
        }
    }

    /**
     * sets symbol entities of a start term in main module scope
     * @return TypeTerm of start term
     */
    public HaskellObject checkBasicTerm(HaskellExp exp){
        if (this.ccg == null){
           return null;
        } else {
           BasicTermTypeInferenceVisitor tiv = (new BasicTermTypeInferenceVisitor(this.prelude,this.assumptions,this.ccg));
           return tiv.forTerm(exp,this.mainModule);
        }
    }

    /**
     * initialize all structures of the modules
     *
     */
    private void build(){
        this.visit(new NameVisitor(this.prelude));
        this.collectEntities();
        this.buildExportLists();
        this.setSymbolEntity();
        this.visit(new LabeledFieldTranslator(this.prelude));
        this.reducePatLambdaExps();
        this.kindInference(this.buildKindGroups(),this.getInnerTypes());
        this.preTypeToSchema(this.typeRules);
        this.prelude.deriveInstances(this.getModules());
        this.prelude.addDerivingsForTuplesAndBool();
        this.instantiate();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
//        System.out.println("HS: "+HaskellSym.counter);
//        System.out.println("HE: "+HaskellEntity.Skeleton.count);
        }

        this.collectClassConstraints();
        this.ccg.checkInstances();
        for (Module m : this.modMap.values()){
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println(m.getDeclarations().size());
            }

            m.getDeclarations().clear();
            if (m.expList != null) {
                m.expList.clear();
            }
        }

//        this.gc = (new GroupCollector(this.prelude));
//        this.gc.forModules(this);
        Modules.log.log(Level.INFO,"Collect mutual recursive blocks for type inference\n");
        GroupCollector gc = (new GroupCollector(this.prelude));
        gc.forModules(this);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("--------------------------------------------------------");
        }

        this.typeInference();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("--------------------------------------------------------");
            System.out.println("--------------------------------------------------------");
        }
    }

    /**
     * builds the prelude for serialization
     */
    public void buildPrelude(){
        this.prelude.setAccessible(true); // prelude should be typechecked
        this.typeRules = new HashSet<HaskellBasicRule>();
        this.assumptions = new Assumptions.MapSkeleton();
        this.kindAssumptions = new EntityAssumptions();
        this.ccg = new ClassConstraintGraph();
        this.build();
        //this.gc = null;
        this.fullCopy = true;
        this.prelude.setAccessible(false);
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            HaskellSym.showee(this);
        }
    }

    /**
     * builds a HaskellProgram (an obligation)
     */
    public HaskellProgram buildHaskellProgram(){
        this.prelude.setAccessible(false); // prelude is loaded, it is already typechecked
                                           // so set it not accessible for the typechecker

                                           // the same holds for the already loaded modules, which are marked as such
        this.build();
        //this.gc.destroyMainUnreachables();
        this.prelude.setAccessible(true);

        // making the already loaded modules accessible, by setting the already loaded flag to false
        for (Module m : this.getAlreadyLoadedModules()) {
            m.setAlreadyLoaded(false);
        }

        this.fullCopy = false;
        Modules.log.log(Level.INFO,"Destroy all unreachable entities\n");
        //this.determineUnreachables(this.startTerms);
        this.groups = null;
        return new HaskellProgram(this);
        /*
        ClassConstraintGraph ccg = new ClassConstraintGraph();
        this.collectClassConstraints(ccg);
    ccg.checkInstances();
        this.collectGroups();
        HaskellSym.show("Check instances",this);
        System.out.println("--------------------------------------------------------");
        this.typeInference(ccg);
        System.out.println("--------------------------------------------------------");
        System.out.println("--------------------------------------------------------");
        return new HaskellProgram(this);
        */

        /*for(Module m : modMap.values()){
           System.out.println("\nModule "+m.getName());
           for (HaskellEntity e : m.getCollectedEntities()){
              System.out.format("%20s : %7s :: %s \n",e.getName(),e.getSort()+"",e.getType()+"");
           }
        }*/

    }

    /*public Set<HaskellEntity> getUnreachables(){
        if (this.gc != null) {
           return gc.getUnreachables();
        }
        return new HashSet<HaskellEntity>();
    }*/

    public Set<HaskellEntity> getUnreachables(){
        if (this.unreachables != null) {
           return this.unreachables;
        }
        return new HashSet<HaskellEntity>();
    }

/*    private Set<HaskellEntity> determineStartSet(Collection<HaskellExp> sTerms){
        Set<HaskellEntity> start = null;
        if (sTerms.size()>0) {
            start = new HashSet<HaskellEntity>();
            FreeEntityCollector fec = new FreeEntityCollector(start);
            for (HaskellExp exp : sTerms){
                exp.visit(fec);
            }
        }
        return start;
    }*/

    /**
     * collects all unreachable entities (no needed entities)
     * for the current startterms
     */
    public void determineUnreachables(Collection<Pair<HaskellObject,HaskellExp>> sTerms){
        NeededEntitiesCollector nec = new NeededEntitiesCollector(this.prelude,this.assumptions);
        this.unreachables = nec.getUnreachables(this,sTerms);
    }

    /**
     * destroies all unreachable entities
     * so the HaskellProgram is shorten to the requiered functions, datatypes, classes and instances
     */
    public void onlyReachablesPerStartTerms(){
        this.determineUnreachables(this.startTerms);
        for (HaskellEntity e : this.unreachables){

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("Destroy:" +e);
            }

            e.destroy();
        }
        this.ccg.removeEntities(this.unreachables);
        Set<HaskellEntity> used = new HashSet<HaskellEntity>();
        this.visit(new UsedEntityCollector(used));
        this.assumptions.keepOnly(used);
        this.kindAssumptions = null;
        this.groups = null;
        this.typeRules = null;
        this.prelude.reduce(used);
        this.unreachables = null;
    }

    public void onlyReachablesPerStartTermsForView(Collection<Pair<HaskellObject,HaskellExp>> sTerms){
        this.determineUnreachables(sTerms);
    }
}
