package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Qualifiers.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class Prelude extends Module implements HaskellBean{

    private boolean simplePrelude;

    private static Set <String> deriveables = Prelude.buildDerivables();
    private static String names = "uvwxyz";


    private boolean accessible;
    private int nameCount;
    private Set<String> usedNames;
    private Map<Character,String> internNames;
    private Map<String,Integer> nameCounter;

    private TyConsEntity typeArrow;
    private TyConsEntity list;
    private ConsEntity tup2;
    private ConsEntity listCons;
    private ConsEntity listNil;
    private TyConsEntity bool;
    private ConsEntity boolTrue;
    private ConsEntity boolFalse;
    private HaskellNamedSym boolSym;
    private HaskellNamedSym typeArrowSym;
    private boolean hasBoolDerivings;

    private Cons kindArrow;
    private Cons kindStar;

    private Set<HaskellEntity> preludeExportEntities;
    private Set<Integer> tuples;
    private Set<HaskellSym> tupleSyms;
    private Set<HaskellEntity> tupleHasDerivings;
    private Set<HaskellEntity> tupleDerivings;
    private Set<HaskellEntity> preDefTyCons;

    public void reduce(Set<HaskellEntity> used){
        this.preludeExportEntities.clear();
        this.tuples.clear();
        this.tupleSyms.clear();
        this.tupleDerivings.clear();
        this.tupleHasDerivings.clear();
        this.preDefTyCons.retainAll(used);
    }
    private static Set<String> buildDerivables(){
       Set<String> ds = new HashSet<String>();
       ds.add("Enum");
       ds.add("Eq");
       ds.add("Ord");
       ds.add("Bounded");
       ds.add("Ix");
       ds.add("Show");
       ds.add("Read");
       ds.add("LazyTermination");
       return ds;
    }

    public Prelude(){
        super();
        this.simplePrelude = false;
    }

    public Prelude(Object o, boolean simplePrelude){
        super("Prelude",new Vector<HaskellExport>(),new Vector<ImpDecl>(),new Vector<HaskellDecl>());
        this.kindArrow = new Cons(new Sym("->"));
        this.kindStar = new Cons(new Sym("*"));
        this.nameCount = 0;
        this.tup2 = null;
        this.hasBoolDerivings = false;
        this.nameCounter = new HashMap<String,Integer>();
        this.usedNames = new HashSet<String>();
        this.internNames = new HashMap<Character,String>();
        this.preDefTyCons = new HashSet<HaskellEntity>();
        this.tupleSyms = new HashSet<HaskellSym>();
        this.tuples = new HashSet<Integer>();
        this.tupleDerivings = new HashSet<HaskellEntity>();
        this.tupleHasDerivings = new HashSet<HaskellEntity>();
        this.preludeExportEntities = new HashSet<HaskellEntity>();
        this.typeArrow = new TyConsEntity("->",this,null,new Vector<ConsEntity>());
        this.typeArrow.setType(TypeSchema.create(
               this.buildKindArrow(
               this.getKindStar(),
               this.buildKindArrow(this.getKindStar(),this.getKindStar()))));
        this.topEntityMap.add(this.typeArrow);
        this.preludeExportEntities.add(this.typeArrow);
        this.typeArrowSym = new HaskellNamedSym("Prelude","->",this.typeArrow);
        this.typeArrow.setFixity(InfixDecl.FIXITY_RIGHT);

        this.simplePrelude = simplePrelude;
//        if (!this.simplePrelude) {
            this.createList();
//        }


        this.createBool();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("Prelude creation");
        }

    }

    /**
     * Tells whether this is a simple prelude.
     * If this is a simple prelude, nothing is predefined, except for error, negate, and terminator.
     */
    public boolean isSimplePrelude() {
        return this.simplePrelude;
    }


    public void setNameCount(int nameCount){
        this.nameCount = nameCount;
    }

    public int getNameCount(){
        return this.nameCount;
    }

    public void setNameCounter(Map<String,Integer> nameCounter){
        this.nameCounter = nameCounter;
    }

    public Map<String,Integer> getNameCounter(){
        return this.nameCounter;
    }

    public void setUsedNames(Set<String> usedNames){
        this.usedNames = usedNames;
    }

    public Set<String> getUsedNames(){
        return this.usedNames;
    }

    public void setInternNames(Map<Character,String> internNames){
        this.internNames = internNames;
    }

    public Map<Character,String> getInternNames(){
        return this.internNames;
    }

    public void setPreDefTyCons(Set<HaskellEntity> preDefTyCons){
        this.preDefTyCons = preDefTyCons;
    }

    public Set<HaskellEntity> getPreDefTyCons(){
        return this.preDefTyCons;
    }

    public void setTupleSyms(Set<HaskellSym> tupleSyms){
        this.tupleSyms = tupleSyms;
    }

    public Set<HaskellSym> getTupleSyms(){
        return this.tupleSyms;
    }

    public void setTuples(Set<Integer> tuples){
        this.tuples = tuples;
    }

    public Set<Integer> getTuples(){
        return this.tuples;
    }

    public void setTupleDerivings(Set<HaskellEntity> tupleDerivings){
        this.tupleDerivings = tupleDerivings;
    }

    public Set<HaskellEntity> getTupleDerivings(){
        return this.tupleDerivings;
    }

    public void setTupleHasDerivings(Set<HaskellEntity> tupleHasDerivings){
        this.tupleHasDerivings = tupleHasDerivings;
    }

    public Set<HaskellEntity> getTupleHasDerivings(){
        return this.tupleHasDerivings;
    }

    public void setPreludeExportEntities(Set<HaskellEntity> preludeExportEntities){
        this.preludeExportEntities = preludeExportEntities;
    }

    public Set<HaskellEntity> getPreludeExportEntities(){
        return this.preludeExportEntities;
    }

    @Override
    public Object deepcopy(){
        Prelude target = new Prelude();
        this.copyModule(target);
        target.hasBoolDerivings = this.hasBoolDerivings;
        target.kindStar     = Copy.deep(this.kindStar);
        target.kindArrow    = Copy.deep(this.kindArrow);
        target.accessible   = this.accessible;
        target.nameCount    = this.nameCount;
        target.nameCounter  = new HashMap<String,Integer>();
        target.nameCounter.putAll(this.nameCounter);
        target.usedNames    = new HashSet<String>(this.usedNames);
        target.internNames  = new HashMap<Character,String>();
        target.tup2         =  this.tup2;
        target.typeArrow    = (this.typeArrow);
        target.list         = (this.list);
        target.listCons     = (this.listCons);
        target.listNil      = (this.listNil);
        target.bool         = (this.bool);
        target.boolTrue     = (this.boolTrue);
        target.boolFalse    = (this.boolFalse);
        target.boolSym      = Copy.deep(this.boolSym);
        target.tupleSyms    = Copy.deepCol(this.tupleSyms);
        target.typeArrowSym = Copy.deep(this.typeArrowSym);
        target.tupleDerivings = new HashSet<HaskellEntity>(this.tupleDerivings);
        target.tupleHasDerivings = new HashSet<HaskellEntity>(this.tupleHasDerivings);
        target.preludeExportEntities = new HashSet<HaskellEntity>(this.preludeExportEntities);
        target.tuples = new HashSet<Integer>(this.tuples);
        target.preDefTyCons = new HashSet<HaskellEntity>(this.preDefTyCons);

        target.simplePrelude = this.simplePrelude;

        return this.hoCopy(target);
    }

    @Override
    public boolean isPrelude(){
        return true;
    }

    @Override
    public boolean isAccessible(){
        return this.accessible;
    }

    public boolean getAccessible(){
        return this.accessible;
    }

    public void setAccessible(boolean accessible){
        this.accessible = accessible;
    }

    public boolean getHasBoolDerivings(){
        return this.hasBoolDerivings;
    }

    public void setHasBoolDerivings(boolean hasBoolDerivings){
        this.hasBoolDerivings = hasBoolDerivings;
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseModule(this);
        hv.fcaseEntityFrame(this);
        if (hv.guardModuleFullVisit(this)) {
            this.visitIntern(hv);
            this.typeArrow = this.walk(this.typeArrow,hv);
            this.kindStar = this.walk(this.kindStar,hv);
            this.kindArrow = this.walk(this.kindArrow,hv);
            this.list = this.walk(this.list,hv);
            this.listCons = this.walk(this.listCons,hv);
            this.listNil = this.walk(this.listNil,hv);
            this.tup2 = this.walk(this.tup2,hv);
            this.bool = this.walk(this.bool,hv);
            this.boolTrue = this.walk(this.boolTrue,hv);
            this.boolFalse = this.walk(this.boolFalse,hv);
            this.boolSym = this.walk(this.boolSym,hv);
            this.tupleSyms = this.listWalk(this.tupleSyms,hv);
            this.typeArrowSym = this.walk(this.typeArrowSym,hv);
            this.tupleDerivings = this.listWalk(this.tupleDerivings,hv);
            this.tupleHasDerivings = this.listWalk(this.tupleHasDerivings,hv);
            this.preludeExportEntities = this.listWalk(this.preludeExportEntities,hv);
            this.preDefTyCons = this.listWalk(this.preDefTyCons,hv);
        } else {
            if (this.entityMode){
                if (hv.guardEntities(this)){
                    this.topEntityMap = this.walk(this.topEntityMap,hv);
                }
            } else {
                this.expList = this.listWalk(this.expList,hv);
                this.imps = this.listWalk(this.imps,hv);
                this.decls = this.listWalk(this.decls,hv);
            }
        }
        hv.icaseEntityFrame(this);
        return hv.caseModule(this);
    }

    public String correctName(String name){
        StringBuffer res = new StringBuffer();
        for (int i=0;i<name.length();i++){
           String rep = "";
           switch(name.charAt(i)){
              case '<' : rep = "Lt"; break;
              case '>' : rep = "Gt"; break;
              case '.' : rep = "Pt"; break;
              case '=' : rep = "Es"; break;
              case '-' : rep = "Ms"; break;
              case '!' : rep = "Em"; break;
              case '*' : rep = "Sr"; break;
              case '/' : rep = "Fs"; break;
              case '%' : rep = "Pc"; break;
              case '#' : rep = "Hm"; break;
              case ':' : rep = "Cn"; break;
              case '&' : rep = "As"; break;
              case '?' : rep = "Qm"; break;
              case '$' : rep = "Ds"; break;
              case '+' : rep = "Ps"; break;
              case '^' : rep = "Pr"; break;
              case '\\': rep = "Bs"; break;
              case '|' : rep = "Pe"; break;
              default:
                  rep = name.charAt(i)+"";
           }
           res.append(rep);
        }
        res.setCharAt(0,Character.toLowerCase(res.charAt(0)));
        return res.toString();
    }

    public void addUsedName(String name){
        this.usedNames.add(name);
    }

    public boolean nameIsUsed(String name){
        return this.usedNames.contains(name);
    }

    private String getNextName(){
       int cur = this.nameCount;
       this.nameCount++;
       String nname = "";
       do {
           int val = cur % Prelude.names.length();
           nname = Prelude.names.charAt(val)+nname;
           cur = cur - val;
           cur = cur / Prelude.names.length();
       } while (cur>0);
       return nname;
    }

    public String buildUniqueName(){
       String name;
       do {
           name = this.getNextName();
       } while (this.usedNames.contains(name));
       return name;
    }

    public void freshNameFor(HaskellNamedSym sym){
        String name = sym.getNoQualName();
        if (name.charAt(0) == ' ') {
       String newn = this.internNames.get(name.charAt(1));
           String postfix = name.substring(2,name.length());
       if (newn == null) {
           newn = this.buildUniqueName();
           this.internNames.put(name.charAt(1),newn);
       }
           String nname = newn+postfix;
           this.addUsedName(nname);
       sym.setName(nname);
    }
    }

    public String getNextNameFor(String name){
        Integer i = this.nameCounter.get(name);
        int j = (i == null) ? 0 : i.intValue();
        String nname;
        String cname = this.correctName(name);
        do {
           nname = cname+j;
           j++;
        } while (this.usedNames.contains(nname));
        this.nameCounter.put(name,Integer.valueOf(j));
        this.addUsedName(nname);
        return nname;
    }

    public String getFreshNameFor(String name){
        if (!this.usedNames.contains(name)){
            this.addUsedName(name);
            return name;
        }
        return this.getNextNameFor(name);
    }

    @Override
    public void setCollectedEntities(EntityMap entities){
        this.topEntityMap.addAll(entities.values());
        this.entityMode = true;
        HaskellEntity e = this.getEntity(null,"","negate",HaskellEntity.Sort.VAR);
        e.setFixity(InfixDecl.FIXITY_MONO);
        e.setPriority(6);
    }

    public void deriveInstances(Set<Module> mods){
        for (Module m : mods){
            if (m.isAccessible()){
                for (HaskellEntity e : m.getTopEntities()){
                    if (e instanceof TyConsEntity){
                        DataDecl dd = (DataDecl) e.getValue();
                        if (dd != null) {
                            this.addDerivingsFor((TyConsEntity)e,dd,m);
                        }
                    }
                }
            }
    }

    }

    public void addDerivingsFor(TyConsEntity e,DataDecl dd,Module module){
        if (dd.getDerivings() == null) {
            return;
        }
        module.addEntities(this.addDerivingsFor(e,dd,dd.getTypeSchema(),dd.getDerivings().getClassSyms(),module));
    }

    /**
     * generates, adds, and returns the derived instances
     * @see generateDerivedInstEntities
     */
    public Set<DerivedInstEntity> addDerivingsFor(TyConsEntity e,DataDecl dd,TypeSchema ts,Collection<HaskellSym> classes,Module module){
        Set<DerivedInstEntity> derivedInstEntities = this.generateDerivedInstEntities(e, dd, ts, classes, module);
        module.addEntities(derivedInstEntities);
        return derivedInstEntities;
    }


    /**
     * generates the derivings, but does not add them to the module
     * @param e the type to generate the deriving for
     * @param dd the DataDecl of that type (may be null)
     * @param ts the TypeSchema of the type (must not be null)
     * @param classes The classes whose derivings are to be generated
     * @param module the target module for the derivings
     * @return the derived instances
     */
    public Set<DerivedInstEntity> generateDerivedInstEntities(TyConsEntity e,DataDecl dd,TypeSchema ts,Collection<HaskellSym> classes,Module module) {
        Set<DerivedInstEntity> res = new HashSet<DerivedInstEntity>();
        if (classes == null) {
            return res;
        }
        String name = e.getModule().getName()+"."+e.getName();
        //String name = e.getName();
        Set<HaskellSym> vars = ts.getQuantor();
        Set<ClassConstraint> dtccs = ts.getConstraints();
        HaskellType instance = ts.getMatrix();
        for (HaskellSym cl : classes) {
            if (Prelude.deriveables.contains(cl.getName(false))
                    && cl.getEntity().getModule().isPrelude()) {
                ClassConstraint instCC = new ClassConstraint(cl, Copy
                        .deep(instance));
                Set<ClassConstraint> ruleRes = this.buildConstraintsFor(e, cl,
                        vars, name);
                ruleRes.addAll(Copy.deepCol(dtccs));
                ClassConstraintRule ccr = new ClassConstraintRule(instCC,
                        ruleRes);
                module.getModules().getCcg().addRule(ccr);
                DerivedInstEntity die = new DerivedInstEntity(cl.getName(false)
                        + "$" + name, module, new HashSet<HaskellEntity>(),
                        ccr, Copy.deep(ts));
                this.buildFunctionsFor(die, e, cl, name, module);
                if (module.getEntityN(null, "", cl.getName(false) + "$" + name,
                        HaskellEntity.Sort.INST) != null) {
                    HaskellError.output(dd, "instance already derived");
                }
                // module.addEntity(die);
                res.add(die);
            } else {
                HaskellError.output(cl, "instance for class "
                        + cl.getName(false) + " is not derivable");
            }
        }
        return res;
    }





    public void addDerivingsForTuplesAndBool(){
        if (this.simplePrelude) {
            return;
        }

        List<HaskellSym> classes = new Vector<HaskellSym>();
        classes.add(new HaskellNamedSym(this.getEntity(null,"","Eq",HaskellEntity.Sort.TYCLASS)));
        classes.add(new HaskellNamedSym(this.getEntity(null,"","Ord",HaskellEntity.Sort.TYCLASS)));
        classes.add(new HaskellNamedSym(this.getEntity(null,"","Show",HaskellEntity.Sort.TYCLASS)));
        classes.add(new HaskellNamedSym(this.getEntity(null,"","Ix",HaskellEntity.Sort.TYCLASS)));
        classes.add(new HaskellNamedSym(this.getEntity(null,"","Read",HaskellEntity.Sort.TYCLASS)));
        for (HaskellSym nTupleSym : this.tupleSyms){
            int i = nTupleSym.getTuple();

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("??? need derivings for "+i);
            }

            TyConsEntity tce = (TyConsEntity)(nTupleSym.getEntity());
            if ((!this.tupleHasDerivings.contains(tce)) && (i> 0)) {

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    System.out.println("create derivings for "+i);
                }

                HaskellType nTupleType = new Cons(nTupleSym);
                for (int j=0;j<i;j++){
                    nTupleType = new Apply(nTupleType,Var.createFreshVar());
                }
                TypeSchema ts = TypeSchema.create(Copy.deep(nTupleType));
                ts.autoQuantor();
                for (DerivedInstEntity die : this.addDerivingsFor(tce,null,ts,classes,this)){
                    this.addEntity(die);
                    this.tupleDerivings.addAll(die.getSubEntities());
                };
                this.tupleHasDerivings.add(tce);
            }
        }
        classes.add(new HaskellNamedSym(this.getEntity(null,"","Enum",HaskellEntity.Sort.TYCLASS)));
        classes.add(new HaskellNamedSym(this.getEntity(null,"","Bounded",HaskellEntity.Sort.TYCLASS)));
        if (!this.hasBoolDerivings) {
           this.hasBoolDerivings = true;
           this.addDerivingsFor(this.bool,null,this.getBoolTypeSchema(),classes,this);
        }
    }

    public List<Group> getTupleGroups(){
        List<Group> res = new Vector<Group>();
        for (HaskellEntity e : this.tupleDerivings){
            res.add(new Group(e));
        }
        return res;
    }

    protected Set<ClassConstraint> buildConstraintsFor(TyConsEntity tce,HaskellSym cl,Set<HaskellSym> varsyms,String name){
        Set<ClassConstraint> res = new HashSet<ClassConstraint>();
        List<ConsEntity> ces = tce.getConsList();
    if ("Bounded".equals(cl.getName(false))) {
            if (ces.size()>1) {
                for (ConsEntity ce : ces){
                    if (ce.getArity() > 0) {
                        HaskellError.output(cl,"instance for class "+cl.getName(false)+" is not derivable for data type "+name);
                    }
                }
                return res;
            }
    }

        if ("Enum".equals(cl.getName(false))) {
        for (ConsEntity ce : ces){
            if (ce.getArity() > 0) {
                    HaskellError.output(cl,"instance for class "+cl.getName(false)+" is not derivable for data type "+name);
            }
        }
        return res;
    }

        for (HaskellSym varsym : varsyms){
            res.add(new ClassConstraint(cl,new Var(varsym)));
    }

    return res;

    }

    protected IVarEntity buildIVarEntity(CVarEntity cVarEntity,Module module,List<HaskellRule> rules){
        IVarEntity iVarEntity = new IVarEntity(cVarEntity.getName(),module,null,null);
        iVarEntity.setFixity(cVarEntity.getFixity());
        iVarEntity.setPriority(cVarEntity.getPriority());

        Function func = new Function(new HaskellNamedSym(cVarEntity),rules);
        iVarEntity.setValue(new InstFunction(new HaskellNamedSym(cVarEntity),func));
        return iVarEntity;
    }

    protected void buildFunctionsFor(DerivedInstEntity die,TyConsEntity tce, HaskellSym cl,String name,Module module){
        if ("Bounded".equals(cl.getName(false))) {
            List<ConsEntity> ces = tce.getConsList();
            if (ces.size()>1) {
                List<HaskellRule> rules = null;
                EntityFrame eframe = null;
                HaskellEntity e = null;

                eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                rules = new Vector<HaskellRule>();
                rules.add(new HaskellRule(eframe,new Vector<HaskellPat>(),new Cons(new HaskellNamedSym(ces.get(0)))));
                e = this.getEntity(null,"","minBound",HaskellEntity.Sort.VAR);
                die.addEntity(this.buildIVarEntity((CVarEntity)e,module,rules));

                eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                rules = new Vector<HaskellRule>();
                rules.add(new HaskellRule(eframe,new Vector<HaskellPat>(),new Cons(new HaskellNamedSym(ces.get(ces.size()-1)))));
                e = this.getEntity(null,"","maxBound",HaskellEntity.Sort.VAR);
                die.addEntity(this.buildIVarEntity((CVarEntity)e,module,rules));

            } else {
                List<HaskellRule> rules = null;
                EntityFrame eframe = null;
                HaskellEntity e = null;
                ConsEntity ce = ces.get(0);
                HaskellExp exp = null;

                eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                rules = new Vector<HaskellRule>();
                e = this.getEntity(null,"","minBound",HaskellEntity.Sort.VAR);
                exp = new Cons(new HaskellNamedSym(ce));
                for (int i=0;i<ce.getArity();i++){
                    exp = new Apply(exp,new Var(new HaskellNamedSym(e)));
                }
                rules.add(new HaskellRule(eframe,new Vector<HaskellPat>(),exp));
                die.addEntity(this.buildIVarEntity((CVarEntity)e,module,rules));

                eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                rules = new Vector<HaskellRule>();
                e = this.getEntity(null,"","maxBound",HaskellEntity.Sort.VAR);
                exp = new Cons(new HaskellNamedSym(ce));
                for (int i=0;i<ce.getArity();i++){
                    exp = new Apply(exp,new Var(new HaskellNamedSym(e)));
                }
                rules.add(new HaskellRule(eframe,new Vector<HaskellPat>(),exp));
                die.addEntity(this.buildIVarEntity((CVarEntity)e,module,rules));
            }
    }
        if ("Enum".equals(cl.getName(false))) {
                List<HaskellPat> pats = null;
                List<ConsEntity> ces = tce.getConsList();
                List<HaskellRule> rules = null;
                EntityFrame eframe = null;
                HaskellEntity e = null;
                HaskellEntity par_x = null;
                HaskellEntity par_y = null;
                HaskellExp exp = null;
                int i=0;

                rules = new Vector<HaskellRule>();
                e = this.getEntity(null,"","fromEnum",HaskellEntity.Sort.VAR);
                i = 0;
                for (ConsEntity ce : ces){
                    pats = new Vector<HaskellPat>();
                    pats.add(new Cons(new HaskellNamedSym(ce)));
                    exp = new IntegerLit(i);
                    i++;
                    eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    rules.add(new HaskellRule(eframe,pats,exp));
                }
                die.addEntity(this.buildIVarEntity((CVarEntity)e,module,rules));

                rules = new Vector<HaskellRule>();
                e = this.getEntity(null,"","toEnum",HaskellEntity.Sort.VAR);
                i = 0;
                for (ConsEntity ce : ces){
                    pats = new Vector<HaskellPat>();
                    pats.add(new IntegerLit(i));
                    i++;
                    exp = new Cons(new HaskellNamedSym(ce));
                    eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    rules.add(new HaskellRule(eframe,pats,exp));
                }
                die.addEntity(this.buildIVarEntity((CVarEntity)e,module,rules));

                rules = new Vector<HaskellRule>();
                e = this.getEntity(null,"","enumFrom",HaskellEntity.Sort.VAR);
                eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                pats = new Vector<HaskellPat>();

                par_x = new VarEntity("x",module,null,null,true);
                eframe.addEntity(par_x);
                pats.add(new Var(new HaskellNamedSym(par_x)));

                exp = new Var(new HaskellNamedSym(this.getEntity(null,"","enumFromTo",HaskellEntity.Sort.VAR)));
                exp = new Apply(exp,new Var(new HaskellNamedSym(par_x)));
                exp = new Apply(exp,new Cons(new HaskellNamedSym(ces.get(ces.size()-1))));
                rules.add(new HaskellRule(eframe,pats,exp));
                die.addEntity(this.buildIVarEntity((CVarEntity)e,module,rules));
                rules = new Vector<HaskellRule>();


                rules = new Vector<HaskellRule>();
                e = this.getEntity(null,"","enumFromThen",HaskellEntity.Sort.VAR);
                eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                pats = new Vector<HaskellPat>();

                par_x = new VarEntity("x",module,null,null,true);
                eframe.addEntity(par_x);
                pats.add(new Var(new HaskellNamedSym(par_x)));

                par_y = new VarEntity("y",module,null,null,true);
                eframe.addEntity(par_y);
                pats.add(new Var(new HaskellNamedSym(par_y)));

                exp = new Var(new HaskellNamedSym(this.getEntity(null,"","enumFromThenTo",HaskellEntity.Sort.VAR)));
                exp = new Apply(exp,new Var(new HaskellNamedSym(par_x)));
                exp = new Apply(exp,new Var(new HaskellNamedSym(par_y)));
                exp = new Apply(exp,new Cons(new HaskellNamedSym(ces.get(ces.size()-1))));
                rules.add(new HaskellRule(eframe,pats,exp));
                die.addEntity(this.buildIVarEntity((CVarEntity)e,module,rules));
        }
        if ("Ord".equals(cl.getName(false))) {
                List<HaskellPat> pats = null;
                List<ConsEntity> ces = tce.getConsList();
                List<HaskellRule> rules = null;
                EntityFrame eframe = null;
                HaskellExp exp = null;
                HaskellPat pat = null;
                HaskellExp last = null;
                rules = new Vector<HaskellRule>();
                HaskellEntity leq = this.getEntity(null,"","<=",HaskellEntity.Sort.VAR);
                HaskellEntity lt  = this.getEntity(null,"","<",HaskellEntity.Sort.VAR);
                HaskellEntity eq  = this.getEntity(null,"","==",HaskellEntity.Sort.VAR);
                HaskellEntity and  = this.getEntity(null,"","&&",HaskellEntity.Sort.VAR);
                HaskellEntity or  = this.getEntity(null,"","||",HaskellEntity.Sort.VAR);
                int a = 0;
                for (ConsEntity ce1 : ces){
                    int b = 0;
                    for (ConsEntity ce2 : ces) {
                        eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                        pats = new Vector<HaskellPat>();
                        if (a == b) {
                            List<VarEntity> ve1s = new Vector<VarEntity>();
                            List<VarEntity> ve2s = new Vector<VarEntity>();
                            pat = new Cons(new HaskellNamedSym(ce1));
                            for (int i = 0; i < ce1.getArity();i++){
                                VarEntity ve = new VarEntity("x"+i,module,null,null,true);
                                eframe.addEntity(ve);
                                ve1s.add(ve);
                                pat = new Apply(pat,new Var(new HaskellNamedSym(ve)));
                            }
                            pats.add(pat);
                            pat = new Cons(new HaskellNamedSym(ce2));
                            for (int i = 0; i < ce2.getArity();i++){
                                VarEntity ve = new VarEntity("y"+i,module,null,null,true);
                                eframe.addEntity(ve);
                                ve2s.add(ve);
                                pat = new Apply(pat,new Var(new HaskellNamedSym(ve)));
                            }
                            pats.add(pat);

                            int count = ce1.getArity()-1;
                            if (count >= 0) {
                                for (int i = count;i >= 0; i--){
                                    if (i == count){
                                        last = new Var(new HaskellNamedSym(leq));
                                        last = new Apply(last,new Var(new HaskellNamedSym(ve1s.get(i))));
                                        last = new Apply(last,new Var(new HaskellNamedSym(ve2s.get(i))));
                                    } else {
                                        HaskellExp ai_lt_bi = new Var(new HaskellNamedSym(lt));
                                        ai_lt_bi = new Apply(ai_lt_bi,new Var(new HaskellNamedSym(ve1s.get(i))));
                                        ai_lt_bi = new Apply(ai_lt_bi,new Var(new HaskellNamedSym(ve2s.get(i))));

                                        HaskellExp ai_eq_bi = new Var(new HaskellNamedSym(eq));
                                        ai_eq_bi = new Apply(ai_eq_bi,new Var(new HaskellNamedSym(ve1s.get(i))));
                                        ai_eq_bi = new Apply(ai_eq_bi,new Var(new HaskellNamedSym(ve2s.get(i))));
                                        HaskellExp ai_eq_bi_and_last = new Var(new HaskellNamedSym(and));
                                        ai_eq_bi_and_last = new Apply(ai_eq_bi_and_last,ai_eq_bi);
                                        ai_eq_bi_and_last = new Apply(ai_eq_bi_and_last,last);
                                        last = new Var(new HaskellNamedSym(or));
                                        last = new Apply(last,ai_lt_bi);
                                        last = new Apply(last,ai_eq_bi_and_last);
                                    }
                                }
                                exp = last;
                            } else {
                                exp = new Cons(new HaskellNamedSym(this.boolTrue));
                            }
                        } else {
                            pat = new Cons(new HaskellNamedSym(ce1));
                            for (int i = 0; i < ce1.getArity();i++){
                                pat = new Apply(pat,new JokerPat());
                            }
                            pats.add(pat);
                            pat = new Cons(new HaskellNamedSym(ce2));
                            for (int i = 0; i < ce2.getArity();i++){
                                pat = new Apply(pat,new JokerPat());
                            }
                            pats.add(pat);
                            exp = new Cons(new HaskellNamedSym(a <= b ? this.boolTrue : this.boolFalse));
                        }
                        rules.add(new HaskellRule(eframe,pats,exp));
                        b++;
                    }
                    a++;
                }
                die.addEntity(this.buildIVarEntity((CVarEntity)leq,module,rules));
        }
        if ("Eq".equals(cl.getName(false))) {
                List<HaskellPat> pats = null;
                List<ConsEntity> ces = tce.getConsList();
                List<HaskellRule> rules = null;
                EntityFrame eframe = null;
                HaskellExp exp = null;
                HaskellPat pat = null;
                HaskellExp last = null;
                rules = new Vector<HaskellRule>();
                HaskellEntity eq  = this.getEntity(null,"","==",HaskellEntity.Sort.VAR);
                HaskellEntity and  = this.getEntity(null,"","&&",HaskellEntity.Sort.VAR);
                HaskellEntity or  = this.getEntity(null,"","||",HaskellEntity.Sort.VAR);
                int a = 0;
                for (ConsEntity ce1 : ces){
                    int b = 0;
                    for (ConsEntity ce2 : ces) {
                        eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                        pats = new Vector<HaskellPat>();
                        if (a == b) {
                            List<VarEntity> ve1s = new Vector<VarEntity>();
                            List<VarEntity> ve2s = new Vector<VarEntity>();
                            pat = new Cons(new HaskellNamedSym(ce1));
                            for (int i = 0; i < ce1.getArity();i++){
                                VarEntity ve = new VarEntity("x"+i,module,null,null,true);
                                eframe.addEntity(ve);
                                ve1s.add(ve);
                                pat = new Apply(pat,new Var(new HaskellNamedSym(ve)));
                            }
                            pats.add(pat);
                            pat = new Cons(new HaskellNamedSym(ce2));
                            for (int i = 0; i < ce2.getArity();i++){
                                VarEntity ve = new VarEntity("y"+i,module,null,null,true);
                                eframe.addEntity(ve);
                                ve2s.add(ve);
                                pat = new Apply(pat,new Var(new HaskellNamedSym(ve)));
                            }
                            pats.add(pat);
                            int count = ce1.getArity()-1;
                            if (count >= 0) {
                                for (int i = count;i >= 0; i--){
                                    if (i == count){
                                        last = new Var(new HaskellNamedSym(eq));
                                        last = new Apply(last,new Var(new HaskellNamedSym(ve1s.get(i))));
                                        last = new Apply(last,new Var(new HaskellNamedSym(ve2s.get(i))));
                                    } else {
                                        HaskellExp ai_eq_bi = new Var(new HaskellNamedSym(eq));
                                        ai_eq_bi = new Apply(ai_eq_bi,new Var(new HaskellNamedSym(ve1s.get(i))));
                                        ai_eq_bi = new Apply(ai_eq_bi,new Var(new HaskellNamedSym(ve2s.get(i))));
                                        HaskellExp ai_eq_bi_and_last = new Var(new HaskellNamedSym(and));
                                        ai_eq_bi_and_last = new Apply(ai_eq_bi_and_last,ai_eq_bi);
                                        ai_eq_bi_and_last = new Apply(ai_eq_bi_and_last,last);
                                        last = ai_eq_bi_and_last;
                                    }
                                }
                                exp = last;
                            } else {
                                exp = new Cons(new HaskellNamedSym(this.boolTrue));
                            }
                        } else {
                            pat = new Cons(new HaskellNamedSym(ce1));
                            for (int i = 0; i < ce1.getArity();i++){
                                pat = new Apply(pat,new JokerPat());
                            }
                            pats.add(pat);
                            pat = new Cons(new HaskellNamedSym(ce2));
                            for (int i = 0; i < ce2.getArity();i++){
                                pat = new Apply(pat,new JokerPat());
                            }
                            pats.add(pat);
                            exp = new Cons(new HaskellNamedSym(this.boolFalse));
                        }
                        rules.add(new HaskellRule(eframe,pats,exp));
                        b++;
                    }
                    a++;
                }
                die.addEntity(this.buildIVarEntity((CVarEntity)eq,module,rules));
        }
        if ("Show".equals(cl.getName(false))) {
                List<HaskellPat> pats = null;
                List<ConsEntity> ces = tce.getConsList();
                List<HaskellRule> rules = null;
                EntityFrame eframe = null;
                HaskellExp exp = null;
                HaskellPat pat = null;
                HaskellExp last = null;
                rules = new Vector<HaskellRule>();
                HaskellEntity point = this.getEntity(null,"",".",HaskellEntity.Sort.VAR);
                HaskellEntity wgt  = this.getEntity(null,"",">",HaskellEntity.Sort.VAR);
                HaskellEntity wget = this.getEntity(null,"",">=",HaskellEntity.Sort.VAR);
                HaskellEntity showsPrec = this.getEntity(null,"","showsPrec",HaskellEntity.Sort.VAR);
                HaskellEntity showParen = this.getEntity(null,"","showParen",HaskellEntity.Sort.VAR);
                HaskellEntity showString = this.getEntity(null,"","showString",HaskellEntity.Sort.VAR);
                //HaskellEntity and  = this.getEntity(null,"","&&",HaskellEntity.Sort.VAR);
//                HaskellEntity or  = this.getEntity(null,"","||",HaskellEntity.Sort.VAR);
                int a = 0;
                for (ConsEntity ce : ces){
                    eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    pats = new Vector<HaskellPat>();
                    VarEntity ved = new VarEntity("d",module,null,null,true);
                    eframe.addEntity(ved);
                    pats.add(new Var(new HaskellNamedSym(ved)));
                    List<VarEntity> ves = new Vector<VarEntity>();
                    pat = new Cons(new HaskellNamedSym(ce));
                    for (int i = 0; i < ce.getArity();i++){
                        VarEntity ve = new VarEntity("x"+i,module,null,null,true);
                        eframe.addEntity(ve);
                        ves.add(ve);
                        pat = new Apply(pat,new Var(new HaskellNamedSym(ve)));
                    }
                    pats.add(pat);
                    if (ce.isInfix()) {
                        int prio = ce.getPriority();
                        int prio1 = prio+1;
                        int prio2 = prio+1;
                        HaskellExp dgtp = new Apply(new Apply(new Var(new HaskellNamedSym(wgt)),
                                                              new Var(new HaskellNamedSym(ved))),
                                                    new IntegerLit(prio));
                        switch(ce.getFixity()){
                            case InfixDecl.FIXITY_LEFT :   prio1 = prio; prio2 = prio+1;   break;
                            case InfixDecl.FIXITY_RIGHT :  prio1 = prio+1; prio2 = prio;   break;
                        }
                        HaskellExp showsPrec_prio1_x1 = new Apply(new Apply(new Var(new HaskellNamedSym(showsPrec)),
                                                                           new IntegerLit(prio1)),
                                                              new Var(new HaskellNamedSym(ved)));
                        HaskellExp showString_Name = new Apply(new Var(new HaskellNamedSym(showString)),this.makeString(" "+ce.getName()+" "));
                        HaskellExp showsPrec_prio2_x2 = new Apply(new Apply(new Var(new HaskellNamedSym(showsPrec)),
                                                                           new IntegerLit(prio2)),
                                                              new Var(new HaskellNamedSym(ved)));
                        HaskellExp showStr = showsPrec_prio2_x2;
                        showStr = new Apply( new Apply(new Var(new HaskellNamedSym(point)),
                                                       showString_Name),
                                                       showStr);
                        showStr = new Apply( new Apply(new Var(new HaskellNamedSym(point)),
                                                       showsPrec_prio1_x1),
                                                       showStr);
                        HaskellExp showParen_dgtp_showStr = new Apply(new Apply(new Var(new HaskellNamedSym(showParen)),
                                                                                dgtp),
                                                                    showStr);
                        exp = showParen_dgtp_showStr;
                    } else {
                        HaskellExp dget10 = new Apply(new Apply(new Var(new HaskellNamedSym(wgt)),
                                                            new Var(new HaskellNamedSym(ved))),
                                                    new IntegerLit(10));
                        HaskellExp showString_Name = new Apply(new Var(new HaskellNamedSym(showString)),this.makeString(ce.getName()+" "));
                        HaskellExp showStr = null;
                        int count = ce.getArity()-1;
                        for (int i = count;i >= -1; i--){
                            HaskellExp next = null;
                            if (i > -1) {
                                next = new Apply(  new Apply(new Var(new HaskellNamedSym(showsPrec)),
                                                            new IntegerLit(10)),
                                                    new Var(new HaskellNamedSym(ves.get(i))));
                            } else {
                                next = showString_Name;
                            }
                            if (showStr != null) {
                                showStr = new Apply( new Apply(new Var(new HaskellNamedSym(point)),
                                                                next),
                                                    showStr);
                            } else {
                                showStr = next;
                            }
                        }
                        HaskellExp showParen_dget10_showStr = new Apply(new Apply(new Var(new HaskellNamedSym(showParen)),
                                                                                dget10),
                                                                    showStr);
                        exp = showParen_dget10_showStr;
                    }
                    rules.add(new HaskellRule(eframe,pats,exp));
                }
                die.addEntity(this.buildIVarEntity((CVarEntity)showsPrec,module,rules));
        }

        if ("Read".equals(cl.getName(false))) {
            List<HaskellPat> pats = null;
            List<ConsEntity> ces = tce.getConsList();
            List<HaskellRule> rules = null;
            EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
            HaskellExp exp = null;
            HaskellExp last = null;
            rules = new Vector<HaskellRule>();
            HaskellEntity tup = this.tup2;
            HaskellEntity point = this.getEntity(null,"",".",HaskellEntity.Sort.VAR);
            HaskellEntity wgt  = this.getEntity(null,"",">",HaskellEntity.Sort.VAR);
            HaskellEntity wget = this.getEntity(null,"",">=",HaskellEntity.Sort.VAR);
            HaskellEntity readsPrec = this.getEntity(null,"","readsPrec",HaskellEntity.Sort.VAR);
            HaskellEntity readParen = this.getEntity(null,"","readParen",HaskellEntity.Sort.VAR);
            HaskellEntity lex = this.getEntity(null,"","lex",HaskellEntity.Sort.VAR);
            HaskellEntity plusPlus = this.getEntity(null,"","++",HaskellEntity.Sort.VAR);
            HaskellEntity concatMap = this.getEntity(null,"","concatMap",HaskellEntity.Sort.VAR);
            HaskellEntity emptyList = this.getEntity(null,"","[]",HaskellEntity.Sort.CONS);
            HaskellEntity listCons = this.getEntity(null,"",":",HaskellEntity.Sort.CONS);
            //HaskellEntity and  = this.getEntity(null,"","&&",HaskellEntity.Sort.VAR);
//            HaskellEntity or  = this.getEntity(null,"","||",HaskellEntity.Sort.VAR);
            int a = 0;

            VarEntity d = new VarEntity("d",module,null,null,true);
            eframe.addEntity(d);
            VarEntity r = new VarEntity("r",module,null,null,true);
            eframe.addEntity(r);

            for (ConsEntity ce : ces){
                a++;
                HaskellExp consReadParenExp;
                HaskellExp gtExp;
                HaskellExp lambdaExp = null;
                int prec;

                EntityFrame lambdaEframe = new EntityFrame.EntityFrameSkeleton(eframe,new EntityMap());
                VarEntity lr = new VarEntity("lr"+a,module,null,null,true);
                lambdaEframe.addEntity(lr);
                List<HaskellPat> lPatterns = new Vector<HaskellPat>();
                lPatterns.add(new Var(new HaskellNamedSym(lr)));
                List<HaskellQual> quals = new Vector<HaskellQual>();
                HaskellExp lastPat = new Cons(new HaskellNamedSym(ce));
                if (ce.isInfix()) {
                    prec = ce.getPriority();
                    List<Var> rvars = this.createFreshVarList("r",ce.getArity()+1,module);
                    List<Var> pvars = this.createFreshVarList("p",ce.getArity(),module);
                    Var oldrvar = new Var(new HaskellNamedSym(lr));
                    {
                        HaskellExp gexp = new Apply(new Apply(new Var(new HaskellNamedSym(readsPrec)),new IntegerLit(prec+1)),oldrvar);
                        oldrvar = rvars.remove(0);
                        Var pvar =  pvars.remove(0);
                        HaskellPat gpat = (HaskellPat) this.buildTuple(tup,(HaskellExp) pvar,Copy.deep(oldrvar));
                        quals.add(new GenQual(gpat,gexp));
                        lastPat = new Apply(lastPat,Copy.deep(pvar));
                    }

                    {
                        HaskellExp gexp = new Apply(new Var(new HaskellNamedSym(lex)),oldrvar);
                        oldrvar = rvars.remove(0);
                        HaskellPat gpat = (HaskellPat) this.buildTuple(tup,(HaskellExp) this.makeString(ce.getName()),Copy.deep(oldrvar));
                        quals.add(new GenQual(gpat,gexp));
                    }
                    {
                        HaskellExp gexp = new Apply(new Apply(new Var(new HaskellNamedSym(readsPrec)),new IntegerLit(prec+1)),oldrvar);
                        oldrvar = rvars.remove(0);
                        Var pvar =  pvars.remove(0);
                        HaskellPat gpat = (HaskellPat) this.buildTuple(tup,(HaskellExp) pvar,Copy.deep(oldrvar));
                        quals.add(new GenQual(gpat,gexp));
                        lastPat = new Apply(lastPat,Copy.deep(pvar));
                    }
                    lastPat = this.buildTuple(tup,lastPat,oldrvar);
                } else {
                    prec = 9;
                    HaskellExp lexR = new Apply(new Var(new HaskellNamedSym(lex)), new Var(new HaskellNamedSym(lr)));
                    List<Var> rvars = this.createFreshVarList("r",ce.getArity()+1,module);
                    List<Var> pvars = this.createFreshVarList("p",ce.getArity(),module);
                    Var oldrvar = rvars.remove(0);
                    HaskellPat pat = (HaskellPat) this.buildTuple(tup,(HaskellExp) this.makeString(ce.getName()),Copy.deep(oldrvar));
                    quals.add(new GenQual(pat,lexR));
                    for(int i=0; i<ce.getArity(); ++i) {
                        HaskellExp gexp = new Apply(new Apply(new Var(new HaskellNamedSym(readsPrec)),new IntegerLit(prec+1)),oldrvar);
                        oldrvar = rvars.remove(0);
                        Var pvar =  pvars.remove(0);
                        HaskellPat gpat = (HaskellPat) this.buildTuple(tup,(HaskellExp) pvar,Copy.deep(oldrvar));
                        lastPat = new Apply(lastPat,Copy.deep(pvar));
                        quals.add(new GenQual(gpat,gexp));
                    }
                    lastPat = this.buildTuple(tup,lastPat,oldrvar);
                }

                HaskellExp lExp = ListCompFactory.buildListComp(lastPat, quals, concatMap, listCons,emptyList, module, lambdaEframe);
                lambdaExp = new LambdaExp(lPatterns,lExp,lambdaEframe);
                gtExp = new Apply(new Apply(new Var(new HaskellNamedSym(wgt)), new Var(new HaskellNamedSym(d))), new IntegerLit(prec));
                consReadParenExp = new Apply(new Var(new HaskellNamedSym(readParen)), gtExp);
                consReadParenExp = new Apply(consReadParenExp, lambdaExp);
                consReadParenExp = new Apply(consReadParenExp, new Var(new HaskellNamedSym(r)));

                if (exp == null) {
                    exp = consReadParenExp;
                } else {
                    exp = new Apply(new Apply(new Var(new HaskellNamedSym(plusPlus)), exp), consReadParenExp);
                }
            }
            pats = new Vector<HaskellPat>();
            pats.add(new Var(new HaskellNamedSym(d)));
            pats.add(new Var(new HaskellNamedSym(r)));
            rules.add(new HaskellRule(eframe,pats,exp));
            die.addEntity(this.buildIVarEntity((CVarEntity)readsPrec,module,rules));
        }
        if ("Ix".equals(cl.getName(false))) {
            List<ConsEntity> ces = tce.getConsList();
            HaskellExp exp = null;
            HaskellEntity tup = this.tup2;
            HaskellEntity point = this.getEntity(null,"",".",HaskellEntity.Sort.VAR);
            HaskellEntity wgt  = this.getEntity(null,"",">",HaskellEntity.Sort.VAR);
            HaskellEntity wget = this.getEntity(null,"",">=",HaskellEntity.Sort.VAR);
            HaskellEntity range = this.getEntity(null,"","range",HaskellEntity.Sort.VAR);
            HaskellEntity index = this.getEntity(null,"","index",HaskellEntity.Sort.VAR);
            HaskellEntity inRange = this.getEntity(null,"","inRange",HaskellEntity.Sort.VAR);
            HaskellEntity mul = this.getEntity(null,"","*",HaskellEntity.Sort.VAR);
            HaskellEntity rangeSize = this.getEntity(null,"","rangeSize",HaskellEntity.Sort.VAR);
            HaskellEntity plus = this.getEntity(null,"","+",HaskellEntity.Sort.VAR);
            HaskellEntity minus = this.getEntity(null,"","-",HaskellEntity.Sort.VAR);
            HaskellEntity concatMap = this.getEntity(null,"","concatMap",HaskellEntity.Sort.VAR);
            HaskellEntity emptyList = this.getEntity(null,"","[]",HaskellEntity.Sort.CONS);
            HaskellEntity listCons = this.getEntity(null,"",":",HaskellEntity.Sort.CONS);
            HaskellEntity and  = this.getEntity(null,"","&&",HaskellEntity.Sort.VAR);
            HaskellEntity sum  = this.getEntity(null,"","sum",HaskellEntity.Sort.VAR);
            HaskellEntity map  = this.getEntity(null,"","map",HaskellEntity.Sort.VAR);
            HaskellEntity error = this.getEntity(null,"","error",HaskellEntity.Sort.VAR);
            if (ces.size()==1){
                for (ConsEntity ce : ces){
                    EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    List<HaskellQual> quals = new Vector<HaskellQual>();
                    List<Var> xvars = this.createFreshVarList("x",ce.getArity(),module);
                    List<Var> yvars = this.createFreshVarList("y",ce.getArity(),module);
                    HaskellPat zpat = new Cons(new HaskellNamedSym(ce));
                    HaskellPat xpat =  new Cons(new HaskellNamedSym(ce));
                    HaskellPat ypat =  new Cons(new HaskellNamedSym(ce));
                    for(Var zvar : this.createFreshVarList("z",ce.getArity(),module)){
                        Var xvar = xvars.remove(0);
                        Var yvar = yvars.remove(0);
                        eframe.addEntity(xvar.getSymbol().getEntity());
                        eframe.addEntity(yvar.getSymbol().getEntity());
                        HaskellExp ra = this.buildTuple(tup,(HaskellExp)xvar,(HaskellExp)yvar);
                        HaskellExp gexp = new Apply(new Var(new HaskellNamedSym(range)),ra);
                        zpat = new Apply(zpat,Copy.deep(zvar));
                        ypat = new Apply(ypat,Copy.deep(yvar));
                        xpat = new Apply(xpat,Copy.deep(xvar));
                        quals.add(new GenQual(zvar,gexp));
                    }
                    List<HaskellPat> pats = new Vector<HaskellPat>();
                    pats.add((HaskellPat) this.buildTuple(tup,(HaskellExp)xpat,(HaskellExp)ypat));
                    List<HaskellRule> rules = new Vector<HaskellRule>();
                    rules.add(new HaskellRule(eframe,pats,ListCompFactory.buildListComp((HaskellExp)zpat, quals, concatMap, listCons,emptyList, module, eframe)));
                    die.addEntity(this.buildIVarEntity((CVarEntity)range,module,rules));
                }
                for (ConsEntity ce : ces){
                    EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    List<Var> xvars = this.createFreshVarList("x",ce.getArity(),module);
                    List<Var> yvars = this.createFreshVarList("y",ce.getArity(),module);
                    HaskellPat zpat = new Cons(new HaskellNamedSym(ce));
                    HaskellPat xpat =  new Cons(new HaskellNamedSym(ce));
                    HaskellPat ypat =  new Cons(new HaskellNamedSym(ce));
                    exp = null;
                    for(Var zvar : this.createFreshVarList("z",ce.getArity(),module)){
                        Var xvar = xvars.remove(0);
                        Var yvar = yvars.remove(0);
                        eframe.addEntity(xvar.getSymbol().getEntity());
                        eframe.addEntity(yvar.getSymbol().getEntity());
                        eframe.addEntity(zvar.getSymbol().getEntity());
                        HaskellExp ra = this.buildTuple(tup,(HaskellExp)xvar,(HaskellExp)yvar);
                        HaskellExp ira = new Apply(new Apply(new Var(new HaskellNamedSym(inRange)),ra),zvar);
                        if (exp == null) {
                            exp = ira;
                        } else {
                            exp = new Apply(new Apply(new Var(new HaskellNamedSym(and)),ira),exp);
                        }
                        zpat = new Apply(zpat,Copy.deep(zvar));
                        ypat = new Apply(ypat,Copy.deep(yvar));
                        xpat = new Apply(xpat,Copy.deep(xvar));
                    }
                    List<HaskellPat> pats = new Vector<HaskellPat>();
                    pats.add((HaskellPat) this.buildTuple(tup,(HaskellExp)xpat,(HaskellExp)ypat));
                    pats.add(zpat);
                    List<HaskellRule> rules = new Vector<HaskellRule>();
                    rules.add(new HaskellRule(eframe,pats,exp));
                    die.addEntity(this.buildIVarEntity((CVarEntity)inRange,module,rules));
                }

                for (ConsEntity ce : ces){
                    EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    List<Var> xvars = this.createFreshVarList("x",ce.getArity(),module);
                    List<Var> yvars = this.createFreshVarList("y",ce.getArity(),module);
                    HaskellPat zpat = new Cons(new HaskellNamedSym(ce));
                    HaskellPat xpat =  new Cons(new HaskellNamedSym(ce));
                    HaskellPat ypat =  new Cons(new HaskellNamedSym(ce));
                    exp = null;
                    for(Var zvar : this.createFreshVarList("z",ce.getArity(),module)){
                        Var xvar = xvars.remove(0);
                        Var yvar = yvars.remove(0);
                        eframe.addEntity(xvar.getSymbol().getEntity());
                        eframe.addEntity(yvar.getSymbol().getEntity());
                        eframe.addEntity(zvar.getSymbol().getEntity());
                        HaskellExp ra = this.buildTuple(tup,(HaskellExp)xvar,(HaskellExp)yvar);
                        HaskellExp ind = new Apply(new Apply(new Var(new HaskellNamedSym(index)),ra),zvar);
                        if (exp == null) {
                            exp = ind;
                        } else {
                            HaskellExp raS = new Apply(new Var(new HaskellNamedSym(rangeSize)),Copy.deep(ra));
                            exp = new Apply(new Apply(new Var(new HaskellNamedSym(mul)),raS),exp);
                            exp = new Apply(new Apply(new Var(new HaskellNamedSym(plus)),ind),exp);
                        }
                        zpat = new Apply(zpat,Copy.deep(zvar));
                        ypat = new Apply(ypat,Copy.deep(yvar));
                        xpat = new Apply(xpat,Copy.deep(xvar));
                    }
                    List<HaskellPat> pats = new Vector<HaskellPat>();
                    pats.add((HaskellPat) this.buildTuple(tup,(HaskellExp)xpat,(HaskellExp)ypat));
                    pats.add(zpat);
                    List<HaskellRule> rules = new Vector<HaskellRule>();
                    rules.add(new HaskellRule(eframe,pats,exp));
                    die.addEntity(this.buildIVarEntity((CVarEntity)index,module,rules));
                }
            } else {
                {
                    EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    VarEntity x = new VarEntity("x",module,null,null,true);
                    Var xvar = new Var(new HaskellNamedSym(x));
                    eframe.addEntity(x);
                    VarEntity y = new VarEntity("y",module,null,null,true);
                    Var yvar = new Var(new HaskellNamedSym(y));
                    eframe.addEntity(y);
                    VarEntity z = new VarEntity("z",module,null,null,true);
                    Var zvar = new Var(new HaskellNamedSym(z));
                    eframe.addEntity(z);
                    List<HaskellPat> pats = new Vector<HaskellPat>();
                    pats.add((HaskellPat) this.buildTuple(tup,(HaskellExp)xvar,(HaskellExp)yvar));
                    pats.add((HaskellPat) zvar);
                    List<HaskellRule> rules = new Vector<HaskellRule>();
                    exp = new Apply(new Apply(new Var(new HaskellNamedSym(wget)),Copy.deep(yvar)),Copy.deep(zvar));
                    exp = new Apply(new Apply(new Var(new HaskellNamedSym(and)),exp),new Apply(new Apply(new Var(new HaskellNamedSym(wget)),Copy.deep(zvar)),Copy.deep(xvar)));
                    rules.add(new HaskellRule(eframe,pats,exp));
                    die.addEntity(this.buildIVarEntity((CVarEntity)inRange,module,rules));
                }
                {
                    EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    VarEntity x = new VarEntity("x",module,null,null,true);
                    Var xvar = new Var(new HaskellNamedSym(x));
                    eframe.addEntity(x);
                    VarEntity y = new VarEntity("y",module,null,null,true);
                    Var yvar = new Var(new HaskellNamedSym(y));
                    eframe.addEntity(y);
                    VarEntity z = new VarEntity("z",module,null,null,true);
                    Var zvar = new Var(new HaskellNamedSym(z));
                    eframe.addEntity(z);
                    List<HaskellPat> pats = new Vector<HaskellPat>();
                    pats.add((HaskellPat) this.buildTuple(tup,(HaskellExp)xvar,(HaskellExp)yvar));
                    pats.add((HaskellPat) zvar);
                    exp = new Apply(new Apply(new Var(new HaskellNamedSym(wget)),Copy.deep(yvar)),Copy.deep(zvar));
                    exp = new Apply(new Apply(new Var(new HaskellNamedSym(and)),exp),new Apply(new Apply(new Var(new HaskellNamedSym(wget)),Copy.deep(zvar)),Copy.deep(xvar)));
                    EntityFrame leframe = new EntityFrame.EntityFrameSkeleton(eframe,new EntityMap());
                    VarEntity s = new VarEntity("s",module,null,null,true);
                    leframe.addEntity(s);
                    List<HaskellPat> lpats = new Vector<HaskellPat>();
                    lpats.add(new Var(new HaskellNamedSym(s)));
                    HaskellExp cond = new Apply(new Apply(new Var(new HaskellNamedSym(wgt)),Copy.deep(yvar)),new Var(new HaskellNamedSym(s)));
                    HaskellExp lambdaExp = new LambdaExp(lpats,new IfExp(cond,new IntegerLit(1),new IntegerLit(0)),leframe);
                    HaskellExp ra = new Apply (new Var(new HaskellNamedSym(range)) ,this.buildTuple(tup,(HaskellExp)Copy.deep(xvar),(HaskellExp)Copy.deep(yvar)));
                    HaskellExp maprange = new Apply(new Apply(new Var(new HaskellNamedSym(map)),lambdaExp),ra);
                    HaskellExp indmapr = new Apply(new Var(new HaskellNamedSym(sum)),maprange);
                    exp = new IfExp(exp,indmapr,(HaskellExp)new Apply(new Var(new HaskellNamedSym(error)),this.makeString("")));
                    List<HaskellRule> rules = new Vector<HaskellRule>();
                    rules.add(new HaskellRule(eframe,pats,exp));
                    die.addEntity(this.buildIVarEntity((CVarEntity)index,module,rules));
                }
                {
                    EntityFrame eframe = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
                    VarEntity x = new VarEntity("x",module,null,null,true);
                    Var xvar = new Var(new HaskellNamedSym(x));
                    eframe.addEntity(x);
                    VarEntity y = new VarEntity("y",module,null,null,true);
                    Var yvar = new Var(new HaskellNamedSym(y));
                    eframe.addEntity(y);
                    List<HaskellPat> pats = new Vector<HaskellPat>();
                    pats.add((HaskellPat) this.buildTuple(tup,(HaskellExp)xvar,(HaskellExp)yvar));

                    EntityFrame leframe = new EntityFrame.EntityFrameSkeleton(eframe,new EntityMap());
                    VarEntity z = new VarEntity("z",module,null,null,true);
                    Var zvar = new Var(new HaskellNamedSym(z));
                    leframe.addEntity(z);
                    List<HaskellPat> lpats = new Vector<HaskellPat>();
                    lpats.add((HaskellPat) zvar);
                    HaskellExp cond = new Apply(new Apply(new Var(new HaskellNamedSym(wget)),Copy.deep(yvar)),Copy.deep(zvar));
                    cond = new Apply(new Apply(new Var(new HaskellNamedSym(and)),cond),new Apply(new Apply(new Var(new HaskellNamedSym(wget)),Copy.deep(zvar)),Copy.deep(xvar)));
                    HaskellExp trueExp = new Apply(new Apply(new Cons(new HaskellNamedSym(listCons)),Copy.deep(zvar)),new Cons(new HaskellNamedSym(emptyList)));
                    HaskellExp lambdaExp = new LambdaExp(lpats,new IfExp(cond,trueExp,new Cons(new HaskellNamedSym(emptyList))),leframe);
                    HaskellExp lis = new Cons(new HaskellNamedSym(emptyList));
                    ListIterator<ConsEntity> it = ces.listIterator(ces.size());
                    while (it.hasPrevious()){
                        ConsEntity ce =  it.previous();
                        lis = new Apply(new Apply(new Cons(new HaskellNamedSym(listCons)),new Cons(new HaskellNamedSym(ce))),lis);
                    }
                    exp = new Apply(new Apply(new Var(new HaskellNamedSym(concatMap)),lambdaExp),lis);
                    List<HaskellRule> rules = new Vector<HaskellRule>();
                    rules.add(new HaskellRule(eframe,pats,exp));
                    die.addEntity(this.buildIVarEntity((CVarEntity)range,module,rules));
                }

            }
        }
        if ("LazyTermination".equals(cl.getName(false))) {
            this.addLazyTerminationDeriving(die, tce, cl, name, module);
        }
    }






    private transient Set<Pair<Module, HaskellEntity>> lazyGenFuncs = null;

    /**
     * Gets and clears the set of functions that were created
     * while creating the derived InstEntities for the LazyTermination class.
     * @return the created (normal) functions together with their module
     */
    public Set<Pair<Module,HaskellEntity>> getAndClearLazyGenFuncs() {
        Set<Pair<Module,HaskellEntity>> res = this.lazyGenFuncs;
        this.lazyGenFuncs = null;
        return res;
    }

    /**
     * derives the LazyTermination instance for a type
     * @param die The DerivedInstEntity to fill the rules into
     * @param tce The type to generate the LazyTermination instance for
     * @param cl Should be "LazyTermination" symbol
     * @param name Should be "LazyTermination"
     * @param module The module to add the deriving to (usually the main module)
     */
    private void addLazyTerminationDeriving(DerivedInstEntity die,TyConsEntity tce, HaskellSym cl,String name,Module module) {
        List<HaskellPat> patsLT = null;
        List<HaskellPat> patsLG = null;
        List<ConsEntity> ces = tce.getConsList();
        List<HaskellRule> rulesLT = null;
        List<HaskellRule> rulesLG = null;
        EntityFrame eframeLT = null;
        EntityFrame eframeLG = null;
        HaskellExp expLT = null;
        HaskellExp expLG = null;
        HaskellPat patLT = null;
        HaskellPat patLG = null;
        HaskellExp lastLT = null;
        HaskellExp lastLG = null;
        rulesLT = new Vector<HaskellRule>();
        HaskellEntity lazyT = this.getEntity(null, "", "lazyTerminating", HaskellEntity.Sort.VAR);
        HaskellEntity lazyG = this.getEntity(null, "", "lazyGenerator", HaskellEntity.Sort.VAR);
        HaskellEntity termi = this.getEntity(null, "", "terminator", HaskellEntity.Sort.VAR);
        HaskellEntity and   = this.getEntity(null,"","&&",HaskellEntity.Sort.VAR);
        HaskellEntity nat_Z = this.getEntity(null, "", "Zero", HaskellEntity.Sort.CONS);
        HaskellEntity nat_S = this.getEntity(null, "", "Succ", HaskellEntity.Sort.CONS);

        // every term is 0-terminating
        //  => lazyTerminating Z _ = True
        eframeLT = new EntityFrame.EntityFrameSkeleton(module, new EntityMap());
        patsLT = new ArrayList<HaskellPat>();
        patsLT.add(new Cons(new HaskellNamedSym(nat_Z)));
        VarEntity joker = new VarEntity("x", module, null, null, true);
        eframeLT.addEntity(joker);
        patsLT.add(new Var(new HaskellNamedSym(joker)));
        rulesLT.add(new HaskellRule(eframeLT, patsLT, new Cons(new HaskellNamedSym(this.boolTrue))));

        boolean isFirst = true;

        // a term starting with a constructor
        for (ConsEntity ce : ces){
            eframeLT = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
            eframeLG = new EntityFrame.EntityFrameSkeleton(module,new EntityMap());
            patsLT = new Vector<HaskellPat>();
            VarEntity ne = new VarEntity("n", module, null, null, true);
            patLT = new Apply(new Cons(new HaskellNamedSym(nat_S)), new Var(new HaskellNamedSym(ne)));
            patsLT.add(patLT);
            List<VarEntity> ves = new Vector<VarEntity>();
            patLT = new Cons(new HaskellNamedSym(ce));
            for (int i = 0; i < ce.getArity();i++){
                VarEntity ve = new VarEntity("x"+i,module,null,null,true);
                eframeLT.addEntity(ve);
                ves.add(ve);
                patLT = new Apply(patLT,new Var(new HaskellNamedSym(ve)));
            }
            patsLT.add(patLT);

            VarEntity lazyGen_i = null;
            if (!isFirst) {
                lazyGen_i = new VarEntity(this.getFreshNameFor("lazyGenerator_"+ce.getName()), module, null, null);
                //module.addEntity(lazyGen_i);

                if (this.lazyGenFuncs == null) {
                    this.lazyGenFuncs = new HashSet<Pair<Module,HaskellEntity>>();
                }
                this.lazyGenFuncs.add(new Pair<Module,HaskellEntity>(module,lazyGen_i));
            }

            int count = ce.getArity()-1;

            if (count >= 0) {
                for (int i = count;i >= 0; i--){
                    if (i == count){
                        lastLT = new Var(new HaskellNamedSym(lazyT));
                        lastLT = new Apply(lastLT, new Var(new HaskellNamedSym(ne)));
                        lastLT = new Apply(lastLT,new Var(new HaskellNamedSym(ves.get(i))));

                        expLG = new Apply(new Cons(new HaskellNamedSym(ce)), new Var(new HaskellNamedSym(lazyG)));
                    } else {
                        HaskellExp lazyT_n_ti = new Var(new HaskellNamedSym(lazyT));
                        lazyT_n_ti = new Apply(lazyT_n_ti, new Var(new HaskellNamedSym(ne)));
                        lazyT_n_ti = new Apply(lazyT_n_ti,new Var(new HaskellNamedSym(ves.get(i))));
                        HaskellExp lazyT_n_ti_and_last = new Var(new HaskellNamedSym(and));
                        lazyT_n_ti_and_last = new Apply(lazyT_n_ti_and_last,lazyT_n_ti);
                        lazyT_n_ti_and_last = new Apply(lazyT_n_ti_and_last,lastLT);
                        lastLT = lazyT_n_ti_and_last;

                        expLG = new Apply(expLG, new Var(new HaskellNamedSym(lazyG)));
                    }

                    /*
                    lg = lg1 termi
                    lg1 True = C1 lg ... lg
                    lg1 False = lg2 termi
                    lg2 True = C2 lg ... lg
                    lg2 False = l3 termi
                    ...
                    lgn _ = Cn lg ... lg
                    */
                }
                expLT = lastLT;
            } else {
                expLT = new Cons(new HaskellNamedSym(this.boolTrue));
                expLG = new Cons(new HaskellNamedSym(ce));
            }
            rulesLT.add(new HaskellRule(eframeLT,patsLT,expLT));


            if (isFirst) {
                // the last step is simply the constructor term
                isFirst = false;
                lastLG = expLG;
            }
            else {
                rulesLG = new ArrayList<HaskellRule>(2);

                eframeLG = new EntityFrame.EntityFrameSkeleton(module, new EntityMap());
                patLG = new Cons(new HaskellNamedSym(this.getBoolTrue()));
                patsLG = new ArrayList<HaskellPat>(1);
                patsLG.add(patLG);
                HaskellRule hr = new HaskellRule(eframeLG, patsLG, expLG);
                rulesLG.add(hr);

                eframeLG = new EntityFrame.EntityFrameSkeleton(module, new EntityMap());
                patLG = new Cons(new HaskellNamedSym(this.getBoolFalse()));
                patsLG = new ArrayList<HaskellPat>(1);
                patsLG.add(patLG);
                hr = new HaskellRule(eframeLG, patsLG, lastLG);
                rulesLG.add(hr);

                Function f = new Function(new HaskellNamedSym(lazyGen_i), rulesLG);
                lazyGen_i.setValue(f);
                lastLG = new Apply(new Var(new HaskellNamedSym(lazyGen_i)), new Var(new HaskellNamedSym(termi)));
            }
        }
        die.addEntity(this.buildIVarEntity((CVarEntity)lazyT,module,rulesLT));

        eframeLG = new EntityFrame.EntityFrameSkeleton(module, new EntityMap());
        rulesLG = new ArrayList<HaskellRule>(1);
        HaskellRule hr = new HaskellRule(eframeLG, new ArrayList<HaskellPat>(), lastLG);
        rulesLG.add(hr);
        die.addEntity(this.buildIVarEntity((CVarEntity)lazyG, module, rulesLG));
    }
















    public List<Var> createFreshVarList(String basename, int count, Module module){
        Vector<Var> vars = new Vector<Var>();
        for (int i=0;i< count;i++){
            VarEntity e = new VarEntity(basename+i,module,null,null,true);
            vars.add(new Var(new HaskellNamedSym(e)));
        }
        return vars;
    }
    public HaskellExp buildTuple(HaskellEntity e, HaskellExp... pars){
        HaskellSym sym = new HaskellNamedSym(e);
        sym.setTuple(pars.length);
        HaskellExp exp = new Cons(sym);
        for (int i=0;i<pars.length;i++){
            exp = new Apply(exp,pars[i]);
        }
        return exp;
    }

    public HaskellExp makeString(String str){
       HaskellExp exp = new Cons(new HaskellNamedSym(this.listNil));
       for (int i=str.length();i>0;i--){
           exp = new Apply(new Apply(new Cons(new HaskellNamedSym(this.listCons)),
                                     new CharLit(str.charAt(i-1))),
                           exp);
       }
       return exp;
    }

    @Override
    public void buildExportEntities(){
        super.buildExportEntities();
        this.newExpEntities.addAll(this.preludeExportEntities);
    }

    public Set<HaskellEntity> getPreDefEntities(){
        return this.preludeExportEntities;
    }

    public void createList(){
       HaskellSym tyConsSym = new HaskellNamedSym("Prelude","[]",null);

       Var nvar = Var.createFreshVar();
       TypeSchema nConsTypeSchema = TypeSchema.create(this.buildArrow(nvar,this.buildArrow(new Apply(new Cons(tyConsSym),nvar),new Apply(new Cons(tyConsSym),nvar))));
       nConsTypeSchema.autoQuantor();
       Vector<Boolean> strictness = new Vector<Boolean>();
       strictness.add(false);
       strictness.add(false);
       this.listCons = new ConsEntity(":",this,null,nConsTypeSchema,strictness,true,false);
       this.listCons.setFixity(InfixDecl.FIXITY_RIGHT);
       this.listCons.setPriority(5);

       this.linkEntityMap.add(this.listCons);
       this.preludeExportEntities.add(this.listCons);

       TypeSchema nNilTypeSchema = TypeSchema.create(new Apply(new Cons(tyConsSym),Var.createFreshVar()));
       nNilTypeSchema.autoQuantor();
       this.listNil = new ConsEntity("[]",this,null,nNilTypeSchema,new Vector<Boolean>(),false,false);
       this.linkEntityMap.add(this.listNil);
       this.preludeExportEntities.add(this.listNil);

       this.list = new TyConsEntity("[]",this,null,new Vector<ConsEntity>());
       this.list.addCons(this.listCons);
       this.list.addCons(this.listNil);
       HaskellType nListKind = this.buildKindArrow(this.getKindStar(),this.getKindStar());
       this.list.setType(TypeSchema.create(nListKind));
       tyConsSym.setEntity(this.list);
       this.topEntityMap.add(this.list);
       this.preludeExportEntities.add(this.list);
       this.preDefTyCons.add(this.list);
    }

    public void createTuple(int i){
       if (this.tuples.contains(i)) {
        return;
    }
       this.tuples.add(i);
       HaskellSym tyConsSym = new HaskellNamedSym("Prelude","@"+i,null);
       tyConsSym.setTuple(i);
       HaskellType nTupleKind = this.getKindStar();
       HaskellType nTupleType = new Cons(tyConsSym);
       Vector<Boolean> strictness = new Vector<Boolean>();
       Var[] vars = new Var[i];
       for (int j=0;j<i;j++){
           strictness.add(false);
           vars[i-j-1] = Var.createFreshVar();
           nTupleType = new Apply(nTupleType,vars[i-j-1]);
       }
       for (int j=0;j<i;j++){
            nTupleKind = this.buildKindArrow(this.getKindStar(),nTupleKind);
            nTupleType = this.buildArrow(vars[j],nTupleType);
       }

       TypeSchema nTupleTypeSchema = TypeSchema.create(nTupleType);
       nTupleTypeSchema.autoQuantor();
       ConsEntity nTupleCons = new ConsEntity("@"+i,this,null,nTupleTypeSchema,strictness,false,true);
       if (i==2){
           this.tup2 = nTupleCons;
       }
       this.linkEntityMap.add(nTupleCons);
       this.preludeExportEntities.add(nTupleCons);

       TyConsEntity nTuple = new TyConsEntity("@"+i,this,null,new Vector<ConsEntity>());
       nTuple.addCons(nTupleCons);
       nTuple.setType(TypeSchema.create(nTupleKind));
       tyConsSym.setEntity(nTuple);
       this.preludeExportEntities.add(nTuple);
       this.topEntityMap.add(nTuple);
       this.preDefTyCons.add(nTuple);
       this.tupleSyms.add(tyConsSym);
    }

    public void createBool(){
       this.boolSym = new HaskellNamedSym("Prelude","Bool",null);
       HaskellType boolKind = this.getKindStar();
       this.boolTrue = new ConsEntity("True",this,null,this.getBoolTypeSchema(),new Vector<Boolean>(),false,false);
       this.linkEntityMap.add(this.boolTrue);
       this.preludeExportEntities.add(this.boolTrue);
       this.boolFalse = new ConsEntity("False",this,null,this.getBoolTypeSchema(),new Vector<Boolean>(),false,false);
       this.linkEntityMap.add(this.boolFalse);
       this.preludeExportEntities.add(this.boolFalse);
       this.bool = new TyConsEntity("Bool",this,null,new Vector<ConsEntity>());
       this.bool.addCons(this.boolFalse);
       this.bool.addCons(this.boolTrue);
       this.bool.setType(TypeSchema.create(boolKind));
       this.boolSym.setEntity(this.bool);
       this.topEntityMap.add(this.bool);
       this.preludeExportEntities.add(this.bool);
       this.preDefTyCons.add(this.bool);
    }

    public HaskellExp createTrue(){
        return new Cons(new HaskellNamedSym("Prelude","True",this.boolTrue));
    }

    public ImpDecl createPreludeImpDecl(boolean quali){
       return new ImpDecl(quali,new HaskellNamedSym("Prelude"),null,null);
    }

    public ImpDecl createAlreadyLoadedImpDecl(boolean quali, String moduleName) {
        return new ImpDecl(quali, new HaskellNamedSym(moduleName), null,null);
    }

    public HaskellObject buildApply(HaskellObject f,HaskellObject x){
        //if (!((BasicTerm)deArrow(f.getTypeTerm()).get(0)).equivalentTo(x.getTypeTerm())) {
        //    throw new RuntimeException("Apply typeArrow");
        //}
        return (new Apply(f,x)).setTypeTerm((HaskellType)this.cutFirstArrow(f.getTypeTerm()));
    }

    private HaskellObject cutFirstArrow(HaskellObject a){
        return HaskellTools.applyFlatten(a).get(2);
    }

    public HaskellObject buildApplies(HaskellObject start,List<? extends HaskellObject> hos){
        for (HaskellObject ho : hos){
            start = this.buildApply(start,ho);
        }
        return start;
    }

    public HaskellType buildArrow(HaskellType f,HaskellType x){
        return new Apply(new Apply(new Cons(this.getTypeArrowSym()),f),x);
    }

    public HaskellType buildArrows(List<HaskellType> hts){
        ListIterator<HaskellType> it = hts.listIterator(hts.size());
        HaskellType cur = it.previous();
        while(it.hasPrevious()){
           cur = this.buildArrow(it.previous(),cur);
        }
        return cur;
    }

    public HaskellType buildArrows(List<HaskellType> hts,HaskellType res){
        ListIterator<HaskellType> it = hts.listIterator(hts.size());
        while(it.hasPrevious()){
           res = this.buildArrow(it.previous(),res);
        }
        return res;
    }

    public HaskellType buildKindArrow(HaskellType a, HaskellType b){
        return (HaskellType) new Apply(new Apply(this.kindArrow,a),b);
    }

    public List<HaskellType> deArrow(HaskellType a){
        return this.deArrow(a,new Cons(this.getTypeArrowSym()));
    }

    public List<HaskellType> deKindArrow(HaskellType a){
        return this.deArrow(a,this.getKindArrow());
    }

    private List<HaskellType> deArrow(HaskellType a,HaskellType ar){
        List<HaskellType> res = new Vector<HaskellType>();
        List<HaskellObject> l = null;
        do {
           l = this.removeOneArrow(a,ar);
           if (l != null) {
              res.add((HaskellType)l.get(0));
              a = (HaskellType) l.get(1);
           } else {
              res.add((HaskellType)a);
           }
        } while (l != null);
        return res;
    }

    // Since only HaskellType objects shoud be in the type, a list of those shall be returned
    @SuppressWarnings("unchecked")
    public List<HaskellType> removeOneTypeArrow(HaskellType type) {
        return (List)this.removeOneArrow(type, new Cons(this.getTypeArrowSym()));
    }

    public List<HaskellObject> removeOneArrow(HaskellObject a, HaskellType ar){
        List<HaskellObject> list = HaskellTools.applyFlatten(a);
        if (((BasicTerm)list.get(0)).equivalentTo(ar)) {
           list.remove(0);
           return list;
        } else {
           return null;
        }
    }

    public void setTypeArrow(TyConsEntity typeArrow){
        this.typeArrow = typeArrow;
    }

    public TyConsEntity getTypeArrow(){
        return this.typeArrow;
    }

    public void setListCons(ConsEntity listCons){
        this.listCons = listCons;
    }

    public ConsEntity getListCons(){
        return this.listCons;
    }

    public void setListNil(ConsEntity listNil){
        this.listNil = listNil;
    }

    public ConsEntity getListNil(){
        return this.listNil;
    }

    public void setBoolTrue(ConsEntity boolTrue){
        this.boolTrue = boolTrue;
    }

    public ConsEntity getBoolTrue(){
        return this.boolTrue;
    }

    public void setBoolFalse(ConsEntity boolFalse){
        this.boolFalse = boolFalse;
    }

    public ConsEntity getBoolFalse(){
        return this.boolFalse;
    }

    public void setTypeArrowSym(HaskellNamedSym typeArrowSym){
        this.typeArrowSym = typeArrowSym;
    }

    public HaskellNamedSym getTypeArrowSym(){
        return this.typeArrowSym;
    }

    public void setBoolSym(HaskellNamedSym boolSym){
        this.boolSym = boolSym;
    }

    public HaskellNamedSym getBoolSym(){
        return this.boolSym;
    }

    public void setBool(TyConsEntity bool){
        this.bool = bool;
    }

    public TyConsEntity getBool(){
        return this.bool;
    }

    public void setList(TyConsEntity list){
        this.list = list;
    }

    public TyConsEntity getList(){
        return this.list;
    }

    public void setKindArrow(Cons kindArrow){
        this.kindArrow = kindArrow;
    }

    public Cons getKindArrow(){
        return this.kindArrow;
    }

    public void setKindStar(Cons kindStar){
        this.kindStar = kindStar;
    }

    public Cons getKindStar(){
        return this.kindStar;
    }

    public TypeSchema getBoolTypeSchema(){
        TypeSchema ts = TypeSchema.create(new Cons(this.boolSym));
        ts.autoQuantor();
        return ts;
    }

    public HaskellSym createSymbol(String qual,String name){
        return new Symbol(qual,name,this);
    }

    public HaskellSym createSymbolRef(String name,HaskellEntity.Sort sort){
        try {
            HaskellEntity e  = this.getEntity(null,"Prelude",name,sort);
            return new HaskellNamedSym("Prelude",name,e);
        } catch (HaskellError e) {
            HaskellSym.showee(this);
            throw e;
        }
    }

    public static class Symbol extends HaskellNamedSym {
        Prelude prelude;

        public Symbol(){
        }

        public Symbol(String qual,String name,Prelude prelude){
            super(qual,name);
            this.prelude = prelude;
        }

        public void setPrelude(Prelude prelude){
            this.prelude = prelude;
        }

        public Prelude getPrelude(){
            return this.prelude;
        }

        @Override
        public void setEntityPer(EntityFrame ef,HaskellEntity.Sort sort){
             this.setEntity(this.prelude.getLocalEntity(this,sort));
        }
    }

    public static class Sym extends HaskellSym implements HaskellBean{
        String name;

        public Sym(){
        }

        public void setName(String name){
            this.name = name;
        }

        public String getName(){
            return this.name;
        }

        public Sym(String name){
            this.name = name;
        }

        @Override
        public String toString(){
            return this.name;
        }

        @Override
        public String getQualifier(){
            return "Prelude";
        }

    }

}
