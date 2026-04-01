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


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This Visitor collect the groups in each entity frame of a let expression,
 * the top entities of all modules are in one major entity frame.
 * Eeach entity frame is splitted into mutual recusive blocks (groups), these are
 * saved in the HaskellObject carrying the entity frame (concrete Module or LetExp)
 */
public class GroupCollector extends HaskellVisitor {
    public LinkedList<Frame> frames;
    public Set<HaskellEntity> mainUnreachables;
    public Set<HaskellEntity> mainGroup;
    public Set<HaskellEntity> basicGroup;
    public Set<HaskellEntity> unreachables;
    public HaskellDepGraph depGraph;

    HaskellEntity equalEntity;
    HaskellEntity minusEntity;
    HaskellEntity geqEntity;
    HaskellEntity andEntity;
    Prelude prelude;
    boolean pat;


    public GroupCollector(Prelude prelude){
        this.prelude = prelude;
        this.frames = new LinkedList<Frame>();
        this.equalEntity = this.getEntity("==");
        this.minusEntity = this.getEntity("-");
        this.geqEntity   = this.getEntity(">=");
        this.andEntity   = this.getEntity("&&");
        this.pat = false;

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

    @Override
    public HaskellObject casePlusPat(PlusPat ho) {
        this.frames.iterator().next().check(this.geqEntity);
        this.frames.iterator().next().check(this.minusEntity);
        this.frames.iterator().next().check(this.andEntity);
        return ho;
    }

    @Override
    public HaskellObject caseIntegerLit(IntegerLit ho) {
        if (this.pat) {
            this.frames.iterator().next().check(this.equalEntity);
            this.frames.iterator().next().check(this.andEntity);
        }
        return ho;
    }

    @Override
    public HaskellObject caseFloatLit(FloatLit ho) {
        if (this.pat) {
            this.frames.iterator().next().check(this.equalEntity);
            this.frames.iterator().next().check(this.andEntity);
        }
        return ho;
    }

    @Override
    public HaskellObject caseCharLit(CharLit ho) {
        if (this.pat) {
            this.frames.iterator().next().check(this.equalEntity);
            this.frames.iterator().next().check(this.andEntity);
        }
        return ho;
    }

    @Override
    public HaskellObject caseHaskellNamedSym(HaskellNamedSym ho) {
        HaskellEntity e = ho.getEntity();
        if (e.getType() == null) {
            for (Frame frame : this.frames){
                if (frame.check(e)) {
                    return ho;
                }
            }
        }
        return ho;
    }

    @Override
    public void fcaseLetExp(LetExp ho){
        Frame frame = new Frame(ho.getEntityFrame().getCollectedEntities(),this);
        this.frames.add(0,frame);
    frame.run();
    ho.setGroups(frame.buildGroups());
    this.frames.remove(0);
    }

/*    public void forModules(Modules modules){
        Set<HaskellEntity> this.basicGroup = new HashSet<HaskellEntity>();
        Set<HaskellEntity> cvarGroup = new HashSet<HaskellEntity>();
    for (Module m : modules.getModules()){
            for (HaskellEntity e : m.getCollectedEntities()){
                if (e.getSort() == HaskellEntity.Sort.PATDECL){
                        this.basicGroup.add(e);
                } else  if ((e.getSort() == HaskellEntity.Sort.IVAR)){
                        cvarGroup.add(e);
                } else  if (e.getSort() == HaskellEntity.Sort.VAR) {
                        if (e instanceof CVarEntity) {
                        cvarGroup.add(e);
                        } else {
                        this.basicGroup.add(e);
                        }
                }
            }
    }
        Frame frame = new Frame(this.basicGroup,this);
        this.frames.add(0,frame);
    frame.run();
    List<Group> groups = frame.buildGroups();
    for (HaskellEntity e : cvarGroup){
         e.visit(this);
         groups.add(new Group(e));
    }
    modules.setGroups(groups);
    this.frames.remove(0);
    }*/

    /**
     * This <b>must</b> not be called with names other than predefined entities!
     * @return predefined Entity with the given name from the Prelude.
     */
    private HaskellEntity getEntity(String name){
        if (this.prelude.isSimplePrelude()){
            return this.prelude.getEntityN(this,"Prelude",name,HaskellEntity.Sort.VAR);
        }

        return this.prelude.getEntity(this,"Prelude",name,HaskellEntity.Sort.VAR);
    }

    public void forModules(Modules modules){

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("Start group collection");
        }

        this.basicGroup = new HashSet<HaskellEntity>();
        this.mainGroup = new HashSet<HaskellEntity>();
        Set<HaskellEntity> cvarGroup = new HashSet<HaskellEntity>();
        Set<HaskellEntity> ivarGroup = new HashSet<HaskellEntity>();
        for (Module m : modules.getModules()){
            for (HaskellEntity e : m.getCollectedEntities()){
                // **1**
                if (e.getSort() == HaskellEntity.Sort.PATDECL){
                    this.basicGroup.add(e);
                } else  if ((e.getSort() == HaskellEntity.Sort.IVAR)){

                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        //  System.out.println(e.getParentEntity()+" ---> "+e);
                    }

                    ivarGroup.add(e);
                } else  if ((e.getSort() == HaskellEntity.Sort.INST)){
                } else  if ((e.getSort() == HaskellEntity.Sort.TYCLASS)){
                } else  if (e.getSort() == HaskellEntity.Sort.VAR) {
                    if (e instanceof CVarEntity) {
                        cvarGroup.add(e);
                    } else {
                        this.basicGroup.add(e);
                        if (m.isMainModule()){
                              this.mainGroup.add(e);
                        }
                    }
                }
            }
    }
        Frame frame = new Frame(this.basicGroup,this);
        this.frames.add(0,frame);
        frame.addAsNodes(cvarGroup);
        frame.addAsNodes(ivarGroup);
    frame.run();                  // now somethings depend on cvars
    List<Group> groups = frame.buildGroups(); // but no groups for cvars cause they are in no cycle

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.err.println(groups);
        }

        List<Group> cvarGroups = new Vector<Group>();

    for (HaskellEntity e : cvarGroup){
         frame.current = e;
             e.visit(this); // groups in subterms of class entities
         groups.add(new Group(e)); // for each entities a new group
    }

    for (HaskellEntity e : ivarGroup){
             InstFunction ifunc = (InstFunction)e.getValue();
             frame.current = e;
             ifunc.getFunction().visit(this);
         groups.add(new Group(e)); // for each entities a new group
    }

    modules.setGroups(groups);
    this.frames.remove(0);
    }

    public void oforModules(Modules modules){

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("Start group collection");
        }

        this.basicGroup = new HashSet<HaskellEntity>();
        this.mainGroup = new HashSet<HaskellEntity>();
        Set<HaskellEntity> cvarGroup = new HashSet<HaskellEntity>();
        Set<HaskellEntity> classGroup = new HashSet<HaskellEntity>();
        Set<HaskellEntity> ivarGroup = new HashSet<HaskellEntity>();
        Set<HaskellEntity> instGroup = new HashSet<HaskellEntity>();
    for (Module m : modules.getModules()){
            for (HaskellEntity e : m.getCollectedEntities()){
                // **1**
                if (e.getSort() == HaskellEntity.Sort.PATDECL){
                    this.basicGroup.add(e);
                } else  if ((e.getSort() == HaskellEntity.Sort.IVAR)){

                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        System.out.println(e.getParentEntity()+" ---> "+e);
                    }

                    ivarGroup.add(e);
                } else  if ((e.getSort() == HaskellEntity.Sort.INST)){
                    instGroup.add(e);
                } else  if ((e.getSort() == HaskellEntity.Sort.TYCLASS)){
                    classGroup.add(e);
                } else  if (e.getSort() == HaskellEntity.Sort.VAR) {
                    if (e instanceof CVarEntity) {
                        cvarGroup.add(e);
                    } else {
                        this.basicGroup.add(e);
                        if (m.isMainModule()){
                              this.mainGroup.add(e);
                        }
                    }
                }
            }
    }
        Frame frame = new Frame(this.basicGroup,this);
        this.frames.add(0,frame);
        frame.addAsNodes(cvarGroup);
        frame.addAsNodes(ivarGroup);
    frame.run();                  // now somethings depend on cvars
    List<Group> groups = frame.buildGroups(); // but no groups for cvars cause they are in no cycle
        List<Group> cvarGroups = new Vector<Group>();

        frame.addAsNodes(classGroup);
        frame.addAsNodes(instGroup);
    for (HaskellEntity e : cvarGroup){
         frame.current = e;
             e.visit(this); // groups in subterms of class entities
         cvarGroups.add(new Group(e)); // for each entities a new group
             frame.addEdge(e,e.getParentEntity()); // member depend on class
    }

    for (HaskellEntity e : instGroup){
             frame.addEdge(((InstEntity) e).getTyClassEntity(),e); //class depend on instance
        }

    for (HaskellEntity e : ivarGroup){
             InstFunction ifunc = (InstFunction)e.getValue();
             frame.current = e;
             ifunc.getFunction().visit(this);
             frame.addEdge(ifunc.getMemberForInst(),e); // cvar depends on ivar
         cvarGroups.add(new Group(e)); // for each entities a new group
    }

        groups.addAll(cvarGroups); // cvar groups are possible dependent on normal function
                                    // so they are the last groups in the hierachie
                                    // yes of course other symbols could depend on
                                    // them but the class entities always have a type signature
                                    // given by the user and these groups are for typing
                                    // and not for other stuff.
    modules.setGroups(groups);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("--------------------gggggggggg-");
            System.out.println(groups);
            System.out.println("--dggggggggggggggggg-----------");
        }

        this.depGraph = frame.getDepGraph();
        /*try {
        FileWriter fw = new FileWriter("/home/swiste/graph.dot");
        fw.write(depGraph.toDOT());
        fw.flush();
        fw.close();

        } catch (Exception e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
        }*/

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println(this.mainGroup);
            System.out.println("********************************");
        }

        Set<HaskellEntity> reachables = this.depGraph.determineReachables(this.mainGroup);
        this.basicGroup.addAll(cvarGroup);
        this.basicGroup.addAll(ivarGroup);
        this.basicGroup.addAll(classGroup);
        this.basicGroup.addAll(instGroup);

        this.mainUnreachables = new HashSet<HaskellEntity>(this.basicGroup);
        this.mainUnreachables.removeAll(reachables);
        this.unreachables = new HashSet<HaskellEntity>();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println(reachables);
        }

    this.frames.remove(0);
    }

    public void destroyMainUnreachables(){
        // destroy unrechables standard top variables
        for (HaskellEntity e : this.mainUnreachables){
            e.destroy();
        }
    }

    public void determineUnreachables(Set<HaskellEntity> startGroup){
        if (startGroup == null) {
            this.unreachables = new HashSet<HaskellEntity>();
        } else {
            Set<HaskellEntity> reachables = this.depGraph.determineReachables(startGroup);
            this.unreachables = new HashSet<HaskellEntity>(this.basicGroup);
            this.unreachables.removeAll(reachables);
        }
    }

    public Set<HaskellEntity> getUnreachables(){
        return this.unreachables;
    }

    public void destroyUnreachables(Set<HaskellEntity> startGroup){
        this.determineUnreachables(startGroup);
        for (HaskellEntity e : this.unreachables){
            e.destroy();
        }
    }

    @Override
    public boolean guardDefType(SynTypeDecl ho)        { return false;}
    @Override
    public boolean guardDataType(DataDecl ho)          { return false;}
    @Override
    public boolean guardConss(DataDecl ho)             { return false;}
    @Override
    public boolean guardEntity(HaskellEntity ho)       { return true;}
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
    public boolean guardLetFrame(LetExp ho)            { return false;}
//    public boolean guardPatDeclEntity(PatDeclValue ho) { return true;}
    @Override
    public boolean guardPatDecl(PatDecl ho)            { return false;}
    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) { return false;}
    public boolean oguardApply(Apply ho)                { return true; }
    @Override
    public boolean guardDerivings(DataDecl ho)         {  return false; }

    private static class Frame{
        HaskellDepGraph depGraph;
    HaskellEntity current;
    Set<HaskellEntity> entities;
    GroupCollector gc;

    public Frame(Set<HaskellEntity> entities,GroupCollector gc)  {
        this.entities = entities;
        this.depGraph = new HaskellDepGraph();
        this.gc = gc;
            this.addAsEdgedNodes(this.entities);
    }

        public void addEdge(HaskellEntity a,HaskellEntity b){
            this.depGraph.addEdge(a,b);
        }

        public void addAsEdgedNodes(Set<HaskellEntity> entities){
            for (HaskellEntity e: entities){
           this.depGraph.addNode(e);
           this.depGraph.addEdge(e,e);
        }
        }

        public void addAsNodes(Set<HaskellEntity> entities){
            //this.entities.addAll(entities);
            for (HaskellEntity e: entities){
           this.depGraph.addNode(e);
        }
        }

    public void run(){
        for (HaskellEntity e: this.entities){
                this.current = e;
        e.visit(this.gc);
        }
    }

    public boolean check(HaskellEntity e){
        if (this.entities.contains(e)) {
            this.depGraph.addEdge(this.current,e);
            return true;
        }
        return false;
    }

        public HaskellDepGraph getDepGraph(){
            return this.depGraph;
        }

    List<Group> buildGroups(){
       List<Group> gr = this.depGraph.buildGroups();
       return gr;
    }
    }
}
