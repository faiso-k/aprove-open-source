package aprove.verification.oldframework.Haskell.Collectors;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
 /**
 * @author Stephan Swiderski
 * @version $Id$
 *
 *
 * This visitor collects all entities which are defined in the orginal Haskellprogram
 * somewhere. It walk through every module and generates entities for all forms
 * of declartions. Only for InfixDecls and sometimes TypeDecls no entity is created.
 *
 * Attention: this class is highly dependend on side effects of each HaskellObject
 * and it self.
 *
 * Generally each declaration this visitor visits opens a new Frame and push it one the
 * stack, (if the declaration carries potentially variables) then the
 * subobjects are visit and thereafter the Frame is poped from the stack.
 * the behaviour of the frame is controlled by the flags, which are
 * directly set by the creator.
 */

public class CollectEntitiesVisitor extends HaskellVisitor{
    Stack<Frame> frames;
    Frame curFrame;
    Frame curModuleFrame;
    Module curModule;
    HashMap<String, PreFunction> selectorPreFuncs;

    public void push(Frame frame){
        this.frames.push(frame);
        this.curFrame = frame;
    }

    public void pop(){
        this.frames.pop();
        this.curFrame = this.frames.peek();
    }

    public CollectEntitiesVisitor(){
        this.frames = new Stack<Frame>();
        this.curFrame = null;
        this.curModule = null;
        this.frames.push(null);
        this.selectorPreFuncs = new HashMap<String, PreFunction>();
    }

    public void fcaseHaskellNamedSym(HaskellSym ho) {


    }

    // Var
    @Override
    public void fcaseVar(Var var){
        this.curFrame.addVar(var);
    }


    // Add Decl
    @Override
    public void fcaseAddDecl(AddDecl ho) {
        this.curFrame.seperate();
        this.curFrame.addAddDecl(ho);
    }

    // Type Decl
    @Override
    public void fcaseTypeDecl(TypeDecl ho) {
    }

    @Override
    public HaskellObject caseTypeDecl(TypeDecl ho) {
        this.curFrame.addTypeDecl(ho);
        return ho;
    }

    // --- FuncDecl
    @Override
    public void fcaseFuncDecl(FuncDecl ho) {
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
        this.curFrame.funcSym = ho.getFunction();
        this.curFrame.isCollectLocal = true;
    }

    @Override
    public void icaseFuncDecl(FuncDecl ho) {
        this.curFrame.setEntities();
        this.curFrame.switchOff();
    }

    @Override
    public HaskellObject caseFuncDecl(FuncDecl ho) {
        this.pop();
        this.curFrame.addFuncDecl(ho);
        return ho;
    }

    // --- Pat Decl
    @Override
    public void fcasePatDecl(PatDecl ho) {
        this.curFrame.addPatDecl(ho);
    }

    @Override
    public void icasePatDecl(PatDecl ho) {
        this.curFrame.closePatDecl();
    }

    @Override
    public HaskellObject casePatDecl(PatDecl ho) {
    List<FuncDecl> fds = ho.getFuncDecls();
    for (FuncDecl fd : fds){
        //fd.setPatternMember();
        fd.visit(this);
    }
        return ho;
    }

    // --- CaseAlts
    @Override
    public void fcaseAltExp(AltExp ho) {
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
        this.curFrame.isCollectVar = true;
        this.curFrame.isCollectLocal = true;
    }

    @Override
    public void icaseAltExp(AltExp ho) {
        this.curFrame.setEntities();
        this.curFrame.switchOff();
    }

    @Override
    public HaskellObject caseAltExp(AltExp ho) {
        this.pop();
        return ho;
    }

    // --- Lambda
    @Override
    public void fcaseLambdaExp(LambdaExp ho) {
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
        this.curFrame.isCollectVar = true;
        this.curFrame.isCollectLocal = true;
    }

    @Override
    public void icaseLambdaExp(LambdaExp ho) {
        this.curFrame.setEntities();
        this.curFrame.switchOff();
    }

    @Override
    public HaskellObject caseLambdaExp(LambdaExp ho) {
        this.pop();
        return ho;
    }

    // --- Quantor
    @Override
    public void fcaseQuantorExp(QuantorExp ho) {
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
        this.curFrame.isCollectVar = true;
        this.curFrame.isCollectLocal = true;
    }

    @Override
    public void icaseQuantorExp(QuantorExp ho) {
        this.curFrame.setEntities();
        this.curFrame.switchOff();
    }

    @Override
    public HaskellObject caseQuantorExp(QuantorExp ho) {
        this.pop();
        return ho;
    }

    // --- Let
    @Override
    public void fcaseLetExp(LetExp ho) {
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
    }

    @Override
    public void icaseLetExp(LetExp ho) {
        this.curFrame.setAdditions();
        this.curFrame.setEntities();
        this.curFrame.switchOff();
        ho.setEntityMode(true);
    }

    @Override
    public HaskellObject caseLetExp(LetExp ho) {
        this.pop();
    return ho;
    }

    // --- Module
    @Override
    public void fcaseModule(Module ho) {
        this.curModule = ho;
        this.push(new Frame(ho,ho));
        this.curModuleFrame = this.curFrame;
    }

    @Override
    public HaskellObject caseModule(Module ho) {
        EntityMap es = new EntityMap();
        for (HaskellEntity e : this.curFrame.entities.values()){
            es.add(e);
            if (e.getSort() == HaskellEntity.Sort.TYCLASS || e.getSort() == HaskellEntity.Sort.TYCONS) {
                Set<HaskellEntity> ses = e.getSubEntities();
                if (ses != null){
                    es.addAll(ses);
                }
            }
        }
        this.curFrame.setAdditions(es);
        this.curFrame.setEntities();
        this.selectorPreFuncs.clear();
        this.pop();
        return ho;
    }

    // ---- Default
    @Override
    public void fcaseDefaultDecl(DefaultDecl ho){
        ho.setModule(this.curFrame.curModule);
        this.curFrame.curModule.setDefaultDecl(ho);
    }

    // --- Data
    @Override
    public void fcaseDataDecl(DataDecl ho){
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
        this.curFrame.isCollectTyVar = false;
    }

    @Override
    public void icaseDataDecl(DataDecl ho) {
        this.curFrame.isCollectTyVar = true;
    }

    @Override
    public void iicaseDataDecl(DataDecl ho) {
        this.curFrame.isCollectTyVar = false;
        TyConsEntity tce = new TyConsEntity(ho.getSymbol().getName(true),this.curModule,ho);
        this.curModuleFrame.addEntity(tce);
        this.push(new Frame(this.curModule,tce,this.curFrame.getEntityFrame()));
        this.curFrame.isCollectDataCon = true;
    this.curFrame.curTyConsEntity = tce;
    }

    @Override
    public HaskellObject caseDataDecl(DataDecl ho){
        this.curFrame.setEntities();
        this.pop();
        this.curFrame.setEntities();
        this.pop();
        return ho;
    }

    // --- DataCon
    @Override
    public HaskellObject caseDataCon(DataCon ho){
        this.curFrame.addDataCon(ho, this.curModuleFrame);
        return ho;
    }

    // --- SynTypeDecl
    @Override
    public void fcaseSynTypeDecl(SynTypeDecl ho){
        this.curFrame.addEntity(new TySynEntity(ho.getSymbol().getName(true),this.curModule,ho));
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
        this.curFrame.isCollectTyVar = true;
    }

    @Override
    public void icaseSynTypeDecl(SynTypeDecl ho) {
        this.curFrame.isCollectTyVar = false;
    }

    @Override
    public HaskellObject caseSynTypeDecl(SynTypeDecl ho){
        this.curFrame.setEntities();
        this.pop();
        return ho;
    }

    // --- PreType
    @Override
    public void fcasePreType(HaskellPreType ho){
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        if (!this.curFrame.isCollectDataCon) {
            this.push(new Frame(this.curModule,ef));
            this.curFrame.notUnique = true;
        } else {
            ef.setCollectedEntities(new EntityMap());
        }
    }

    @Override
    public void icasePreType(HaskellPreType ho) {
        if (!this.curFrame.isCollectDataCon) {
            this.curFrame.isCollectTyVar = true;
        }
    }

    @Override
    public HaskellObject casePreType(HaskellPreType ho){
        if (!this.curFrame.isCollectDataCon) {
            this.curFrame.setEntities();
            this.pop();
        }
        return ho;
    }

    // --- Class
    @Override
    public void fcaseClassDecl(ClassDecl ho){
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
    }

    @Override
    public void icaseClassDecl(ClassDecl ho) {
        this.curFrame.isCollectTyVar = true;
    }

    @Override
    public void iicaseClassDecl(ClassDecl ho) {
        this.curFrame.setEntities();
        this.pop();
        TyClassEntity tce = new TyClassEntity(ho.getSymbol().getName(true),this.curModule,ho);
        this.curModuleFrame.addEntity(tce);
        this.push(new Frame(this.curModule,tce,this.curFrame.getEntityFrame()));
        this.curFrame.isClass = true;
    }

    @Override
    public HaskellObject caseClassDecl(ClassDecl ho){
        this.curFrame.setEntities();
        this.pop();
        ho.decls.clear();
        return ho;
    }

    // --- Inst
    @Override
    public void fcaseInstDecl(InstDecl ho){
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(this.curFrame.getEntityFrame());
        ho.setEntityFrame(ef);
        this.push(new Frame(this.curModule,ef));
    }

    @Override
    public void icaseInstDecl(InstDecl ho) {
        this.curFrame.isCollectTyVar = true;
    }

    @Override
    public void iicaseInstDecl(InstDecl ho) {
//        this.curFrame.isCollectTyVar = false;
        this.curFrame.setEntities();
        this.pop();

        InstEntity ie = new InstEntity(ho.getName(),this.curModule,ho);
        this.curModuleFrame.addEntity(ie);
        this.push(new Frame(this.curModule,ie,this.curFrame.getEntityFrame()));
        this.curFrame.isInst = true;
    }

    @Override
    public HaskellObject caseInstDecl(InstDecl ho){
  //      this.curFrame.setEntities();
  //      this.pop();
        this.curFrame.setEntities();
        this.pop();
        ho.decls.clear();
        return ho;
    }

    /**
     * Each frame controles the collection and creation of entities, subentities,
     * and argument entities
     * after a frame is closed the collected entities are transfered to the
     * entitycollector
     */
    public class Frame{
        EntityMap entities;              // collected entities;
        Module curModule;
        EntityCollector entityCollector; // target for the collected entities;
        EntityFrame entityFrame;
        List<AddDecl> adddecls;          // local collected additional declarations,i.e. InfixDecls or TypeDecls
        HaskellSym funcSym;              // the name of the current function
        PreFunction curPreFunc;          // the current function, for which the funcdecls are collected
        PatDeclEntity curPatDeclEntity;  // the entity for the current PatDeclEntity
        PatDecl curPatDecl;              // the current PatDecl, for which the variables are collected
        TyConsEntity curTyConsEntity;    // the current Type Constructor Entity for which DataCons are collected
        boolean isCollectDataCon; // special flag is Datacons are collected in a DataDecl
        boolean isCollectVar;     // variables are collected if it is true
        boolean isCollectTyVar;   // type variables are collected if it is true
        boolean isCollectLocal;   // collected variables are marked as locals
        boolean isClass;          // we are in a ClassDecl
        boolean isInst;           // we are in a InstanceDecl
        boolean notUnique;        // variables could occure more than ones, but we need them collected
        String curPatDeclName;    // name of the expanded pat declaration base variable;


        public Frame(Module mo,EntityCollector entityCollector,EntityFrame entityFrame){
            this.entityCollector = entityCollector;
            this.entityFrame = entityFrame;
            this.entities = new EntityMap();
            this.adddecls = new Vector<AddDecl>();
            this.curModule = mo;
            this.switchOff();
        }

        /**
         * resets the frame completely, in this mode nothing is collected
         */
        public void switchOff(){
            this.curPreFunc = null;
            this.funcSym = null;
            this.curPatDeclEntity = null;
            this.isCollectVar = false;
            this.isCollectTyVar = false;
            this.isCollectLocal = false;
            this.notUnique = false;
            this.isClass = false;
            this.isInst = false;
            this.curPatDecl = null;
            this.curPatDeclName = null;
        }

        public Frame(Module mo,EntityFrame entityFrame){
            this(mo,entityFrame,entityFrame);
        }

        public EntityFrame getEntityFrame(){
            return this.entityFrame;
        }

        public TyConsEntity getCurTyConsEntity() {
            return this.curTyConsEntity;
        }

        public void seperate(){
            this.curPreFunc = null;
        }

        public void addFuncDecl(FuncDecl fd){
            if ((this.curPreFunc != null) && (this.curPreFunc.matchAdd(fd))) {
                return;
            }

            // checking that a selector occurs only with one type
            if (fd instanceof SelectorDecl) {
                PreFunction preFunc = CollectEntitiesVisitor.this.selectorPreFuncs.get(fd.getFunction().getName(false));
                if (preFunc != null) {
                    if (!preFunc.matchAdd(fd)) {
                        HaskellError.output(fd, "different selector with name "+fd.getFunction().getName(false));
                    }
                    return;
                }
            }

            if (this.isInst) {
               this.curPreFunc = new InstPreFunction(fd);
            } else {
               this.curPreFunc = new PreFunction(fd);
            }
            this.curPreFunc.transferToken(fd);
            if (this.isClass || this.isInst) {
               this.setOrBuildVar(fd.getFunction().getName(!this.isInst),this.curModule,this.curPreFunc,null);
            } else {
               VarEntity ve = new VarEntity(fd.getFunction().getName(true),this.curModule,this.curPreFunc,null,false,fd.isPatternMember());
               this.curPreFunc.setEntity(ve);

               // setting the selector so that it can be accessed later
               if (fd instanceof SelectorDecl) {
                   CollectEntitiesVisitor.this.selectorPreFuncs.put(fd.getFunction().getName(false), this.curPreFunc);
               }

               this.addEntity(ve);
            }
        }

        public void addPatDecl(PatDecl pd){
            if (this.isClass || this.isInst) {
               HaskellError.output(pd,"only simple pattern declarations are allowed in classes and instances");
            }

            //this.curPatDeclEntity = new PatDeclEntity(this.curModule,pd,null);
        this.curPatDecl = pd;
            //this.addEntity(this.curPatDeclEntity);
            this.curPatDeclName = this.curPatDecl.startFuncDecl();
        }

        public void addVar(Var var){
            if (this.funcSym != null) {
               if (var.getSymbol() != this.funcSym) {
                  this.addEntity(new VarEntity(var.getSymbol().getName(true),this.curModule,null,null,this.isCollectLocal));
               }
            } else if (this.curPatDecl != null) {
           this.curPatDecl.addFuncDecl(var,this.curPatDeclName);
            } else if (this.isCollectVar) {
               this.addEntity(new VarEntity(var.getSymbol().getName(true),this.curModule,null,null,this.isCollectLocal));
            } else if (this.isCollectTyVar) {
               String name = var.getSymbol().getName(true);
               if (this.notUnique) {
                   if (!this.entities.isDef(name,HaskellEntity.Sort.TYVAR)){
                      this.addEntity(new TyVarEntity(name,this.curModule,null,null));
                   }
               } else {
                   this.addEntity(new TyVarEntity(name,this.curModule,null,null));
               }
            }
        }

        public void addDataCon(DataCon ho, Frame curModuleFrame){
            if (this.isCollectDataCon){
                ConsEntity ce = new ConsEntity(ho.getSymbol().getName(true),this.curModule,ho,ho.getType(),ho.getStrictness(),ho.getFields(),ho.isInfix(),false);
                ho.setType(null);
                this.curTyConsEntity.addCons(ce);
                this.addEntity(ce);
            }
        }


        public void closePatDecl(){
            this.curPatDeclName = null;
            this.curPatDeclEntity = null;
            this.curPatDecl = null;
        }

        public void addEntity(HaskellEntity e){
            if (this.entities.isDef(e.getName(),e.getSort())){
                if (e instanceof SelectorEntity) {
                    return;
                }
                HaskellError.output(e.getValue(),"Already defined: "+e.getName());
            }
            this.entities.add(e);
        }

        public void setOrBuildVar(String name,Module mo,PreFunction value,HaskellObject type){
            HaskellEntity ee = this.entities.get(name,this.isClass ? HaskellEntity.Sort.VAR : HaskellEntity.Sort.IVAR);
            if ((ee != null) && (!(ee instanceof CVarEntity))) {
                HaskellError.output(ee.getValue(),"Already defined: "+ee.getName());
            }
            VarEntity e = (VarEntity) ee;
            if (e == null){
                if (this.isClass) {
                   e = new CVarEntity(name,mo,null,null);
                } else {
                   e = new IVarEntity(name,mo,null,null);
                }
                this.addEntity(e);
            }
            if (type != null) {
               if (e.getType() == null) {
                   e.setType(type);
               } else {
                   HaskellError.output(ee.getValue(),"Already defined: "+ee.getName());
               }
            }
            if (value != null) {
               if (e.getValue() == null) {
                   e.setValue(value);
                   if (this.isClass) {
                       value.setEntity(e);
                   }
               } else {
                   HaskellError.output(ee.getValue(),"Already defined: "+ee.getName());
               }
            }
        }

        public void addAddDecl(AddDecl ad){
            if (this.isInst) {
               HaskellError.output(ad,"infix or type declarations are not allowed in instances");
            }
            if (this.isClass && (ad instanceof TypeDecl)) {
                return;
            }
            this.adddecls.add(ad);
        }

        public void addTypeDecl(TypeDecl td){
            if (this.isClass) {
                for (Var var : td.getVariables()){
                    this.setOrBuildVar(var.getSymbol().getName(false),this.curModule,null,td.getType());
                }
            }
        }

        public void setAdditions(EntityMap entities){
            for (AddDecl ad : this.adddecls){
                ad.transferTo(entities);
            }
        }

        public void setAdditions(){
            this.setAdditions(this.entities);
        }

        public void setEntities(){
            this.entityCollector.setCollectedEntities(this.entities);
        }

    }
}
