package aprove.verification.oldframework.Haskell.Modules;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The Module represents one Haskell code file with file extension "hs",
 * it contains the export list, the import list, the top entities, the top declarations,
 * and the default list (default declarartion).
 */
public class Module extends HaskellObject.HaskellObjectSkeleton implements HaskellBean, HaskellEntity, EntityFrame {
         public static int count = 0;
         public transient int mum;

    String name;
    boolean mainModule;
    List<HaskellDecl> decls;
    List<HaskellExport> expList;
    List<ImpDecl> imps;

    Set<HaskellEntity> expEntities;
    Set<HaskellEntity> newExpEntities;
    EntityMap topEntityMap;
    EntityMap linkEntityMap;

    Modules modules;
    boolean entityMode;

    boolean isAlreadyLoaded;


    /**
     * map of alias to all import qualified and unqualified statements with this alias.
     */
    Map<String,List<ImpDecl>> impQualMap;

    /**
     * map of alias to all unqualified import statements with this alias.
     * (needed for ModExports)
     */
    Map<String,List<ImpDecl>> impMap;

    List<Cons> defaultList;
    DefaultDecl defaultDecl;

    public void setImpQualMap(Map<String,List<ImpDecl>> impQualMap){
        this.impQualMap = impQualMap;
    }

    public Map<String,List<ImpDecl>> getImpQualMap(){
        return this.impQualMap;
    }

    public void setImpMap(Map<String,List<ImpDecl>> impMap){
        this.impMap = impMap;
    }

    public Map<String,List<ImpDecl>> getImpMap(){
        return this.impMap;
    }

    public void setTopEntityMap(EntityMap topEntityMap){
        this.topEntityMap = topEntityMap;
    }

    public EntityMap getTopEntityMap(){
        return this.topEntityMap;
    }

    public void setLinkEntityMap(EntityMap linkEntityMap){
        this.linkEntityMap = linkEntityMap;
    }

    public EntityMap getLinkEntityMap(){
        return this.linkEntityMap;
    }

    public void setExpList(List<HaskellExport> expList){
        this.expList = expList;
    }

    public List<HaskellExport> getExpList(){
        return this.expList;
    }

    public void setExpEntities(Set<HaskellEntity> expEntities){
        this.expEntities = expEntities;
    }

    public Set<HaskellEntity> getExpEntities(){
        return this.expEntities;
    }

    public void setNewExpEntities(Set<HaskellEntity> newExpEntities){
        this.newExpEntities = newExpEntities;
    }

    public Set<HaskellEntity> getNewExpEntities(){
        return this.newExpEntities;
    }

    public void setImps(List<ImpDecl> imps){
        this.imps = imps;
    }

    public List<ImpDecl> getImps(){
        return this.imps;
    }

    public void setDecls(List<HaskellDecl> decls){
        this.decls = decls;
    }

    public List<HaskellDecl> getDecls(){
        return this.decls;
    }

    public void setMainModule(){
        this.mainModule = true;
    }

    public void unsetMainModule() {
        this.mainModule = false;
    }

    public boolean isMainModule(){
        return this.mainModule;
    }

    public boolean getMainModule(){
        return this.mainModule;
    }

    public boolean isAccessible(){
        return !this.isAlreadyLoaded();
    }

    public Module(){
       this.mum = Module.count;
       Module.count++;
    }

    public Module(String name,List<HaskellExport> expList, List<ImpDecl> imps,List<HaskellDecl> decls){
        this();
        this.expList = expList;
        this.imps = imps;
        this.decls = decls;
        this.name = name;
        this.modules = null;

        this.topEntityMap = new EntityMap();
        this.linkEntityMap = new EntityMap();
        this.expEntities = new HashSet<HaskellEntity>();
        this.impMap = new HashMap<String,List<ImpDecl>>();
        this.impQualMap = new HashMap<String,List<ImpDecl>>();

        this.entityMode = false;
        this.defaultList = null;
        this.defaultDecl = null;
    }


    /**
     * deepcopy for a single module is useless
     * it is only for use in modules
     */
    @Override
    public Object deepcopy(){
         Module module = new Module();
         this.copyModule(module);
         return this.hoCopy(module);
    }

    protected void copyModule(Module target){
        DefaultDecl nDD = null;
        List<HaskellDecl> nDecls = new Vector<HaskellDecl>();
        for (HaskellDecl hd : this.decls){
            HaskellDecl nHd = Copy.deep(hd);
            nDecls.add(nHd);
            if (hd == this.defaultDecl){
               nDD = (DefaultDecl) nHd;
            }
        }

        Map<ImpDecl,ImpDecl> iiMap = new HashMap<ImpDecl,ImpDecl>();
        List<ImpDecl> nImps = new Vector<ImpDecl>();
        for (ImpDecl id : this.imps){
            ImpDecl nid = Copy.deep(id);
            nImps.add(nid);
            iiMap.put(id,nid);
        }
        Map<String,List<ImpDecl>> nImpMap = new HashMap<String,List<ImpDecl>>();
        Map<String,List<ImpDecl>> nImpQualMap = new HashMap<String,List<ImpDecl>>();

        for (Map.Entry<String,List<ImpDecl>> entry : this.impMap.entrySet()){
            String alias = entry.getKey();
            List<ImpDecl> aliasList = entry.getValue();
            List<ImpDecl> nAliasList = new Vector<ImpDecl>();
            for (ImpDecl id : aliasList){
               nAliasList.add(iiMap.get(id));
            }
            nImpMap.put(alias,nAliasList);
        }

        for (Map.Entry<String,List<ImpDecl>> entry : this.impQualMap.entrySet()){
            String alias = entry.getKey();
            List<ImpDecl> aliasList = entry.getValue();
            List<ImpDecl> nAliasList = new Vector<ImpDecl>();
            for (ImpDecl id : aliasList){
               nAliasList.add(iiMap.get(id));
            }
            nImpQualMap.put(alias,nAliasList);
        }

        target.name = this.name;
        target.mainModule = this.mainModule;
        target.expList = Copy.deepCol(this.expList);
        target.imps = nImps;
        target.decls = Copy.deepCol(this.decls);
        target.modules = this.modules;

        target.topEntityMap = Copy.deep(this.topEntityMap);
        target.linkEntityMap = Copy.deep(this.linkEntityMap);
        target.expEntities = new HashSet<HaskellEntity>(this.expEntities);
        target.impMap = nImpMap;

        target.impQualMap = nImpQualMap;
        target.defaultList = Copy.deepCol(this.defaultList);
        target.defaultDecl = nDD;
        target.entityMode =  this.entityMode;

        target.isAlreadyLoaded = this.isAlreadyLoaded;
    }

    public boolean isPrelude(){
        return false;
    }

    /**
     * @return True iff this module was already loaded and type-checked
     */
    public boolean isAlreadyLoaded() {
        return this.isAlreadyLoaded;
    }

    /**
     * sets whether this class was loaded and type-checked
     */
    public void setAlreadyLoaded(boolean isAlreadyLoaded) {
        this.isAlreadyLoaded = isAlreadyLoaded;
    }

    public List<Cons> getDefaultList(){
        return this.defaultList;
    }

    public DefaultDecl getDefaultDecl(){
        return this.defaultDecl;
    }

    public void setDefaultDecl(DefaultDecl defaultDecl){
        this.defaultDecl = defaultDecl;
    }

    public void setDefaultList(List<Cons> defaultList){
        this.defaultList = defaultList;
    }

    public void setModules(Modules modules){
        this.modules = modules;
    }

    public Modules getModules(){
        return this.modules;
    }

    @Override
    public void removeEntity(HaskellEntity e){
        this.topEntityMap.remove(e);
        this.linkEntityMap.remove(e);
        this.expEntities.remove(e);
    }

    @Override
    public void destroy(){
        throw new RuntimeException("Not supported");
    }

    public void addLinkEntity(HaskellEntity e){
        this.linkEntityMap.add(e);
    }

    public void addLinkEntities(Collection<HaskellEntity> es){
        for (HaskellEntity e : es) {
            this.addLinkEntity(e);
        }
    }

    public List <HaskellDecl> getDeclarations(){
        return this.decls;
    }

    protected void visitIntern(HaskellVisitor hv){
        this.topEntityMap = this.walk(this.topEntityMap,hv);
        this.linkEntityMap = this.walk(this.linkEntityMap,hv);
        this.expList = this.listWalk(this.expList,hv);
        this.expEntities = this.listWalk(this.expEntities,hv);
        this.imps = this.listWalk(this.imps,hv);
        this.decls = this.listWalk(this.decls,hv);
        this.defaultList = this.listWalk(this.defaultList,hv);
        this.defaultDecl = this.walk(this.defaultDecl,hv);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseModule(this);
        hv.fcaseEntityFrame(this);
        if (hv.guardModuleFullVisit(this)) {
            this.visitIntern(hv);
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

    /**
     * constructs both import maps and determins which modules
     * are also needed.
     */
    public void buildImpMap(){
        Set<String> alreadyLoadedModulesNames = new HashSet<String>(this.modules.getAlreadyLoadedModulesNames());
        alreadyLoadedModulesNames.remove("Prelude");
        Prelude prelude = this.modules.getPrelude();
        if (prelude != null) {
            boolean found = false;
            for (ImpDecl imp : this.imps){
                if ("Prelude".equals(imp.getImportModule())) {
                   found = true;
                }
                else {
                    // check for qualified imports of already loaded modules
                    if ( (imp.isQualified()) && (this.modules.getAlreadyLoadedModulesNames().contains(imp.getImportModule())) ) {
                        alreadyLoadedModulesNames.remove(imp.getImportModule());
                        this.imps.add(prelude.createAlreadyLoadedImpDecl(true, imp.getImportModule()));
                    }
                }
            }
            this.imps.add(prelude.createPreludeImpDecl(found));

            // add unqualified imports for the remaining already loaded modules
            for(String moduleName : alreadyLoadedModulesNames) {
                this.imps.add(prelude.createAlreadyLoadedImpDecl(false, moduleName));
            }
        }

        this.impQualMap.put("",new Vector<ImpDecl>());
        for (ImpDecl imp : this.imps){
            String qual = imp.getAliasQualifier();
            this.modules.addNeededModule(imp.getImportModule());
            if (!imp.isQualified()) {
                this.impQualMap.get("").add(imp);
                List<ImpDecl> aliasList = this.impMap.get(qual);
                if (aliasList == null) {
                    aliasList = new Vector<ImpDecl>();
                    this.impMap.put(qual,aliasList);
                }
                aliasList.add(imp);
            }
            List<ImpDecl> aliasList = this.impQualMap.get(qual);
            if (aliasList == null) {
                aliasList = new Vector<ImpDecl>();
                this.impQualMap.put(qual,aliasList);
            }
            aliasList.add(imp);
        }
    }

    /**
     * @returns the local entities, no imported ones.
     */
    public Set<HaskellEntity> getLocalEntities(){
        Set<HaskellEntity> res = this.topEntityMap.values();
        res.addAll(this.linkEntityMap.values());
        return res;
    }

    /**
     * @returns the local top entities, no imported ones, and no subentities
     *         (ConsEntities, CVarEntities, IVarEntities)
     */
    public Set<HaskellEntity> getTopEntities(){
        Set<HaskellEntity> res = this.topEntityMap.values();
        return res;
    }

    /**
     * @returns the local subentities like ConsEntities, CVarEntities, IVarEntities
     */
    public Set<HaskellEntity> getLinkEntities(){
        Set<HaskellEntity> res = this.linkEntityMap.values();
        return res;
    }

    /**
     * @returns current exported entities, while fixpoint iteration
     *         unstable set.
     */
    public Set<HaskellEntity> getExportEntities(){
        return this.expEntities;
    }

    public void setExportEntities(Set<HaskellEntity> expEntities){
        this.expEntities = expEntities;
    }

    /**
     * one fixpoint iteration step for export entity set
     */
    public void buildExportEntities(){
        this.newExpEntities = new HashSet<HaskellEntity>();
        if (this.expList != null){
            for (HaskellExport exp : this.expList){
                this.newExpEntities.addAll(exp.getExportEntities(this));
            }
        } else {
            this.newExpEntities.addAll(this.getLocalEntities());
        }
    }

    /**
     * compares the old result of the iteration before with the current
     * iteration result and replaces the old result with the new result.
     * @return true if and only if the fixpoint is reached.
     */
    public boolean setNewExportEntities(){
        boolean res;
        if (this.expEntities.size() != this.newExpEntities.size()) {
           res = false;
        } else {
           res = this.expEntities.equals(this.newExpEntities);
        }
        this.expEntities = this.newExpEntities;
        return res;
    }


    /**
     * @return unqualified imported entites for an alias
     */
    public Set<HaskellEntity> getImportEntitiesFor(String qual){
        Set<HaskellEntity> res = new HashSet<HaskellEntity>();
        List<ImpDecl> imps = this.impMap.get(qual);
        if (imps != null) {
           for (ImpDecl imp : imps){
              res.addAll(imp.getImportEntities(this.modules));
           }
        }
        return res;
    }

    /**
     * @return qualified imports !and! unqualified imports ("") for an alias
     */
    public Set<HaskellEntity> getQualImportEntitiesFor(String qual){
        Set<HaskellEntity> res = new HashSet<HaskellEntity>();
        List<ImpDecl> impsForQual = this.impQualMap.get(qual);
        if (impsForQual != null) {
           for (ImpDecl imp : impsForQual){
              res.addAll(imp.getImportEntities(this.modules));
           }
        }
        return res;
    }

    /**
     *  @return qualified imports !and! unqualified imports ("") !and! local,link entities ("" or this.name) for an alias
     */
    public Set<HaskellEntity> getEntitiesFor(String qual){
        Set<HaskellEntity> res = this.getQualImportEntitiesFor(qual);
        if ("".equals(qual) || this.name.equals(qual))  {
           res.addAll(this.topEntityMap.values());
           res.addAll(this.linkEntityMap.values());
        }
        return res;
    }

    /**
     * this function is used normally while the exportlist is build.
     * @return entities matching the qualifier and name, non is allowed for start condition
     * by building the exportlist
     */
    public Set<HaskellEntity> getEntities(String qual,String name,HaskellEntity.Sort sort){
        Set<HaskellEntity> res = new HashSet<HaskellEntity>();
        for (HaskellEntity e : this.getEntitiesFor(qual)){
            if ((e.getSort() == sort) && (name.equals(e.getName()))) { res.add(e); }
        }
        if (res.size()>1) {
            String restext = "";
            for (HaskellEntity e : res){
                restext = restext+" "+e.getModule().getName()+"."+e.getName();
            }

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                HaskellSym.showee(res);
            }

            HaskellError.output(res.iterator().next(),"ambiguous references between"+restext);
        }
        return res;
    }

    /**
     * this function is used normally while the exportlist is build.
     * @return entities matching the qualifier and name of the givem symbol, non is allowed for start condition
     * by building the exportlist
     */
    public Set<HaskellEntity> getEntities(HaskellSym sym,HaskellEntity.Sort sort){
        return this.getEntities(sym.getQualifier(),sym.getName(false),sort);
    }

    /**
     * this function is used normally after exportlist was build
     * @return the only matching entity
     */
    public HaskellEntity getEntity(HaskellObject obj,String qual,String name,HaskellEntity.Sort sort){
        Set<HaskellEntity> res = this.getEntities(qual,name,sort);
        if (res.size()==0) {
            HaskellError.output(obj,"Symbol not found "+qual+"."+name+" in Module "+this.getName());
        }
        return res.iterator().next();
    }

    /**
     * this function is used normally after exportlist was build
     * @return the only matching entity
     */
    public HaskellEntity getEntityN(HaskellObject obj,String qual,String name,HaskellEntity.Sort sort){
        Set<HaskellEntity> res = this.getEntities(qual,name,sort);
        if (res.size()==0) {
            return null;
        }
        return res.iterator().next();
    }

    /**
     * this function is used normally after exportlist was build
     * @return the only matching entity
     */
    public HaskellEntity getEntity(HaskellSym sym,HaskellEntity.Sort sort){
        return this.getEntity(sym,sym.getQualifier(),sym.getName(false),sort);
    }


    // for EntityFrame interface  -----------------------------------------------------------
    @Override
    public void setParentEntityFrame(EntityFrame entityFrame){
    }

    @Override
    public EntityFrame getParentEntityFrame(){
        return null;
    }

    @Override
    public void addEntity(HaskellEntity e){
           this.topEntityMap.add(e);
    }

    public void addEntities(Set<? extends HaskellEntity> hes) {
        this.topEntityMap.addAll((Set<HaskellEntity>)hes);
    }

    @Override
    public HaskellEntity getLocalEntity(HaskellSym sym,HaskellEntity.Sort sort){
        return this.getEntity(sym,sort);
    }

    @Override
    public HaskellEntity getFrameEntity(HaskellSym sym,HaskellEntity.Sort sort){
        if ("".equals(sym.getQualifier())) {
            return this.topEntityMap.get(sym.getName(false),sort);
        }
        return null;
    }

    @Override
    public void setCollectedEntities(EntityMap entities){
        this.topEntityMap = entities;
        this.entityMode = true;
    }

    @Override
    public Set<HaskellEntity> getCollectedEntities(){
        Set res = new HashSet<HaskellEntity>();
        for (HaskellEntity e : this.topEntityMap.values()){
           if (e.getSort() == HaskellEntity.Sort.INST){
              res.addAll(e.getSubEntities());
           }
        }
        res.addAll(this.topEntityMap.values());
        res.addAll(this.linkEntityMap.values());

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println(res);
        }

        return res;
    }

    // for Entity interface --------------------------------------------------------
    public boolean getEntityMode(){
        return this.entityMode;
    }

    public void setEntityMode(boolean entityMode){
        this.entityMode = entityMode;
    }

    public void setName(String name){
        this.name = name;
    }

    @Override
    public String getName(){
        return this.name;
    }

    @Override
    public void setModule(Module module){
    }

    @Override
    public Module getModule(){
        return this;
    }

    public void setSort(HaskellEntity.Sort sort){
    }

    @Override
    public HaskellEntity.Sort getSort(){
        return HaskellEntity.Sort.MODULE;
    }

    @Override
    public int getFixity(){
        return 0;
    }

    @Override
    public int getPriority(){
        return 0;
    }

    @Override
    public void setFixity(int f){
    }

    @Override
    public void setPriority(int p){
    }

    @Override
    public Set<HaskellEntity> getSubEntities(){
        return this.topEntityMap.values();
    }

    public void addSubEntity(HaskellEntity e){
        this.topEntityMap.add(e);
    }

    @Override
    public void setParentEntity(HaskellEntity e){
    }

    @Override
    public HaskellEntity getParentEntity(){
        return null;
    }

    @Override
    public HaskellObject getValue(){
        return null;
    }

    @Override
    public void setValue(HaskellObject value){
    }

    @Override
    public int getTuple(){
        return -1;
    }

    @Override
    public HaskellObject getType(){
        return null;
    }

    @Override
    public void setType(HaskellObject type){
    }


}
