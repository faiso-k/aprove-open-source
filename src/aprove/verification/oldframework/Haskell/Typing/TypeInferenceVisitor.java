package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class TypeInferenceVisitor extends OmegaVisitor {
    Set <HaskellEntity.Sort> VALUESOF = EnumSet.of(HaskellEntity.Sort.VAR,
                                                   HaskellEntity.Sort.IVAR,
                                                   HaskellEntity.Sort.PATDECL);

    ClassConstraintGraph ccg;
    Stack<EntityFrame> arguments;
    List<Cons> defaultList;
    Vector<HaskellObject> typeAnnos = new Vector<HaskellObject>();


    private static long forTimeSum = 0;

    NoQuanStack noQuanStack = new NoQuanStack();
    Stack<Set<ClassConstraint>> constraintStack = new Stack<Set<ClassConstraint>>();

    HaskellSubstitution currentRefine;

    public TypeInferenceVisitor(Prelude prelude,Assumptions assum,ClassConstraintGraph ccg){
        super(assum,prelude);
        this.ccg = ccg;
        this.arguments = new Stack<EntityFrame>();
        this.defaultList = null;
    }

    @Override
    public TypeSchema getTypeSchema(HaskellEntity e){
        if (e.getType() != null) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(e);
                //HaskellSym.showee(e);
            }

            return ((TypeSchema)e.getType()).getFreshInstance();
        }
        TypeSchema ty = this.getAssumptionFor(e);
        return ty.getFreshInstance();
    }

    /**
     * @returns the
     */
    public TypeSchema getAssumptionFor(HaskellEntity e){
    TypeSchema ty = this.assumptions.getTypeSchemaFor(e);
        if (ty == null) {
            ty = TypeSchema.create(Var.createFreshVar());
        this.assumptions.pushAssumption(e,ty);
        }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.err.println("Ask for " +e +" :: "+ty);
        }

        return ty.getFreshInstance();
    }

    @Override
    public HaskellSubstitution mgu(BasicTerm a,BasicTerm b,HaskellObject ho) {
        HaskellSubstitution subs = null;
        BasicTerm ax;
        BasicTerm bx;
        if (this.currentRefine == null) {
            ax = Copy.deep(a);
            bx = Copy.deep(b);
            //subs = BasicTerm.Tools.mgu(,Copy.deep(b));
        } else {
            ax = this.currentRefine.applyTo(a);
            bx = this.currentRefine.applyTo(b);
        }
        //(new Exception()).printStackTrace();
        //System.err.println("mgu1:"+ax);
        //System.err.println("mgu2:"+bx);
        subs = BasicTerm.Tools.mgu(ax,bx);
        //System.err.println("result: "+subs);
        if (subs == null) {
                System.err.println("mgu1:"+ax);
                System.err.println("mgu2:"+bx);
            HaskellSym.showee(new Apply(ax,bx));
                HaskellError.output(ho,"types are not unifiable");
        }
        return subs;
    }


    /**
     * @returns true, iff the group (or mutual recursive block) is restricted
     *          in the way it is defined in the hugs-report.
     */
    public boolean restrictedGroup(Set<HaskellEntity> group){
        for (HaskellEntity e : group){
            if (e.getSort() == HaskellEntity.Sort.PATDECL){
                return true;
            }
            if (e.getSort() == HaskellEntity.Sort.VAR){
                if (e.getValue() instanceof Function){
                   if (((Function) e.getValue()).isSimplePattern()) {
                       if (e.getType() == null) {
                        return true;
                    }
                   }
                }
            }
        }
        return false;
    }


    /**
     * all constraint in the given set share the same type variable
     * and a the ambiguous constraints are only solveable if
     * one of them is the constraint "Num a" which dictates the
     * type variable to solve.
     *
     *
     * @returns the substitution to solve all these class constraints
     *          for the "Num a"-type-variable
     */
    public HaskellSubstitution solveAmbiguousConstraints(Set<ClassConstraint> ccs){
        boolean hasNum = false;
        boolean allPrelude = true;
        for(ClassConstraint cc : ccs){
            //HaskellError.println("ch: "+ cc);
            allPrelude = allPrelude && cc.isInPrelude();
            if (cc.isNumSubClass(this.ccg)) {
                hasNum = true;
                //HaskellError.println("has a number Class constraint");
            }
        }
/*        HaskellError.output = true;
        HaskellError.println("constraints: "+ ccs);
        HaskellError.println("preluded: "+ allPrelude);
        HaskellError.println("num: "+ hasNum);
        HaskellError.println("dll: "+ this.defaultList);*/
        if (hasNum && allPrelude) {
            OuterLoop: for(Cons dt : this.defaultList){
                for(ClassConstraint cc : ccs){
                    if (!cc.solvedBy(dt,this.ccg.getRules())){
                        continue OuterLoop;
                    }
                }
                ClassConstraint cc = ccs.iterator().next();
                return new HaskellSubstitution((Var)cc.getType(),Copy.deep(dt));
            }
            System.err.println();
            return null;
        } else {
            return null;
        }
    }

    /**
     * solves all ambiguous constraints and directly refine the assumptions
     */
    public void solveAllAmbiguousConstraints(HaskellObject ho,Set<Set<ClassConstraint>> ccss){
        //HaskellError.println("Ambiguous: "+ccss);
        this.delayedRefine();
        while (ccss.size()>0){
            Set<ClassConstraint> ccs = ccss.iterator().next();
            ccss.remove(ccs);
            HaskellSubstitution subs = this.solveAmbiguousConstraints(ccs);
            if (subs != null) {
                this.directRefine(subs);
                Set<Set<ClassConstraint>> nccss = new HashSet<Set<ClassConstraint>>();
                for(Set<ClassConstraint> xccs : ccss){
                    Set<ClassConstraint> nccs = new HashSet<ClassConstraint>();
                    for(ClassConstraint cc : xccs){
                        nccs.add(cc.apply(subs));
                    }
                    nccss.add(nccs);
                };
                ccss = nccss;
            } else {
                //System.err.println(this.assumptions);
                HaskellError.output(ho," "+ccs+" Constraint contains ambiguous type variable");
            }
        }
    }

    public void setDefaultList(List<Cons> defaultList){
        this.defaultList = defaultList;
        if (this.defaultList == null) {
            this.defaultList = this.prelude.getDefaultList();
        }
    }

    public void localGroup(Group group,boolean forced){
        //System.err.println("Group:"+group);
        this.delayedRefine();
        int start = this.typeAnnos.size();
        if (!forced && (group.isPreludeGroup() || group.isAlreadyLoadedGroup()) ) {
            return;
        }
        if (group.isMultiGroup()){
            HaskellError.output(group.iterator().next(),"mutual recursive block "+group+" overlaps module borders");
        }
        this.setDefaultList(group.getGroupModule().getDefaultList());
        boolean restricted = this.restrictedGroup(group);
        int[] counts = new int[group.size()];
        int pos = 0;
        for(HaskellEntity e : group){
            int last = this.typeAnnos.size();

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("**********************Typecheck Entity: "+e);
                //System.out.println("Parent:" + e.getParentEntity());
                //System.out.println("Given Type: "+e.getType());
            }

            TypeSchema ts;
            if (e.getValue() != null) {
                this.noQuanStack.pushNewGroup();
                /*
                 * type of e is monomorphic inside of e
                 * (in case there are inner groups)
                 */
                this.noQuanStack.addHoToPeekGroup(this.getAssumptionFor(e));

                e.visit(this);
                this.push(this.getAssumptionFor(e));
                this.push(this.massMgu(2,e));
                this.delayedRefine();
                ts = this.peek();
                this.noQuanStack.popGroup();
                if (restricted) {
                    this.constraintStack.peek().addAll(ts.getConstraints());
                } else {
                    this.reduce(ts.getConstraints());
                    Set<ClassConstraint> scs  = this.removeSurroundingConstraints(ts,this.noQuanStack.unitedGroups());

                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        System.out.println("SCS: "+scs);
                    }

                    this.constraintStack.peek().addAll(scs);
                    // now only the real ambiguous constraints are solved
                    Set<Set<ClassConstraint>> accss = ts.ambiguousConstraints(true);
                    this.solveAllAmbiguousConstraints(e.getValue(),accss);
                    this.reduce(ts.getConstraints());
                    this.ccg.checkConstraints(ts.getConstraints(),e);
                }
                ts = this.pop();
            } else {
                ts = (TypeSchema) e.getType();
            }
            counts[pos] = this.typeAnnos.size()-last;
            this.assumptions.pushAssumption(e,ts);
            pos++;
        }
        this.delayedRefine();
        this.reduce(this.constraintStack.peek());
        this.delayedRefine();
        if (restricted){
            // so the group is restricted (monomorphie restriction)
            // so all constrainted type variables must !NOT! have an allquantor
            // so add them to the noQuanStack
            for (ClassConstraint cc : this.constraintStack.peek()){
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("CC:"+cc);
                }

                this.noQuanStack.addHoToPeekGroup(cc);
            }
            /*for(HaskellEntity e : group){
                TypeSchema ats = this.assumptions.getTypeSchemaFor(e);
                Set <HaskellSym> sres = ats.getConstrainedSyms();
                this.noQuanStack.addToPeekGroup(sres);
            } */
        }

        long forTimeDiff = System.currentTimeMillis();

        pos = 0;
        for(HaskellEntity e : group){
            this.delayedRefine();
            TypeSchema ts = this.assumptions.getTypeSchemaFor(e);
            this.reduce(ts.getConstraints());

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("1Quantified " + e+ "::" + ts);
            }

            int count = counts[pos];

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(e +" :NQB: "+this.noQuanStack);
            }

            if (e.getType() != null) {
                if (restricted) {
                     //HaskellError.output(e,e.getName()+" is in a restricted group, a type signature is not allowed");
                }
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    // System.out.println(ts +" ------ "+e.getType());
                }

                this.push(ts);
                this.specializeWith(e,(TypeSchema) e.getType());
                ts = this.pop();

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("RGiven Type: "+this.assumptions.getTypeSchemaFor(e));
                }
            }

            if (ts.autoQuantor(this.noQuanStack.unitedGroups()) || true){
                // XXX DEBUG
                //if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("     adding");
                //}
                // some type varibales are not allquantified so leave them
                // in the active-typeAnnos-List
                start = start + count;
            } else {
                // the typeAnnotations of entity e are stable
                // cause all type variables are allquantified so no
                // change could occur futher, so remove them from the
                // active-typeAnnos-List
                // XXX DEBUG
                //if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("     remove");
                //}

                this.typeAnnos.subList(start,start+count).clear();
            }
            // now ts has changed and the assumption needs an update
            // so overwrite the assumption for entity e
            this.assumptions.pushAssumption(e,ts);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("2Quantified " + e+ "::" + ts);
            }

            if (!restricted) {
                // all free constraints of ts are transfered to higher level
                // i.e. the type schema of the expression (let groups in exp)
                // has to carry these constraints
                Set<ClassConstraint> fcs = this.getFreeConstraints(ts);

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    System.out.println("Free2 cccc " + e+ "::" + fcs+" -- "+this.constraintStack.peek());
                }

                this.constraintStack.peek().addAll(fcs);
            }

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("______________________________Quantified " + e+ "::" + ts);
            }

            pos++;
        }
        this.delayedRefine();

        forTimeDiff = System.currentTimeMillis() - forTimeDiff;
        TypeInferenceVisitor.forTimeSum += forTimeDiff;

    }

    public Set<ClassConstraint> localGrouping( List<Group> groups,boolean forced){
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //HaskellError.println("****************************");
            //System.out.println("-----------"+groups);
        }

        this.constraintStack.push(new HashSet<ClassConstraint>());
        this.noQuanStack.pushNewGroup();
        //Set<ClassConstraint> res = new HashSet<ClassConstraint>();
        for (Group group : groups) {
            //res.addAll(
            this.localGroup(group,forced);
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("Group result "+groups+" :: "+res);
        }

        this.noQuanStack.popGroup();
        return this.constraintStack.pop();
    }

    /**
     * @returns the set of constraints which contains a type variable
     *          unbounded by the allquantor of the given typeschema
     */
    public Set<ClassConstraint> getFreeConstraints(TypeSchema ts){
        Set<ClassConstraint> cres = new HashSet<ClassConstraint>();
        for (ClassConstraint cc : ts.getConstraints()){
            Set<HaskellSym> csyms = new HashSet<HaskellSym>();
            FreeVarSymCollector cfvsc = new FreeVarSymCollector(csyms);
            cc.visit(cfvsc);
            csyms.removeAll(ts.getQuantor());
            if (csyms.size()>0) {
                cres.add(cc);
            }
        }
        return cres;
    }

    /**
     * removes all Constraints which contains type variables of the surrounding context
     * (type variables in types of function arguments, or local restricted type variables)
     * @returns the set of removed contraints
     */
    public Set<ClassConstraint> removeSurroundingConstraints(TypeSchema ts,Set<HaskellSym> argSyms){
        Set<ClassConstraint> cres = new HashSet<ClassConstraint>();
        Iterator<ClassConstraint> it = ts.getConstraints().iterator();
        while (it.hasNext()){
            ClassConstraint cc = it.next();
            Set<HaskellSym> csyms = new HashSet<HaskellSym>();
            FreeVarSymCollector cfvsc = new FreeVarSymCollector(csyms);
            cc.visit(cfvsc);
            //csyms.removeAll(syms);
            if (csyms.size()>0) {
                csyms.removeAll(argSyms);
                if (csyms.size()==0) {
                    cres.add(cc);
                    it.remove();
                }
            }
        }
        return cres;
    }

    public Set<HaskellEntity> filterEntities(Set<HaskellEntity> inset){
        Set<HaskellEntity> res = new HashSet<HaskellEntity>();
        for (HaskellEntity e : inset){
            if (this.VALUESOF.contains(e.getSort())) {
                res.add(e);
            }
        }
        return res;
    }

    /**
     * @returns a TypeSchema of the form: name a => a  (name is the class name)
     */
    public TypeSchema buildConstraintedTyVar(String name){
        Var nVar = Var.createFreshVar();
        HaskellSym tyCons = this.prelude.createSymbolRef(name,HaskellEntity.Sort.TYCLASS);
        ClassConstraint cc =  new ClassConstraint(tyCons,(HaskellType)nVar);
        Set<ClassConstraint> ccs = new HashSet<ClassConstraint>();
        ccs.add(cc);
        return TypeSchema.create(ccs,(HaskellType)nVar);
    }

    @Override
    public HaskellObject caseCharLit(CharLit ho) {
        this.push(TypeSchema.create(new Cons(this.prelude.createSymbolRef("Char",HaskellEntity.Sort.TYCONS))));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseFloatLit(FloatLit ho) {
        this.push(this.buildConstraintedTyVar("Fractional"));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseIntegerLit(IntegerLit ho) {
        this.push(this.buildConstraintedTyVar("Num"));
        return this.leave(ho);
    }

    @Override
    public HaskellObject casePlusPat(PlusPat ho) {
        this.push(this.buildConstraintedTyVar("Integral"));
        this.push(this.massMgu(3,ho));
        return this.leave(ho);
    }

    /**
     * specialize the current typeschema on stack with the given one
     * it checks first if the typeschema on the stack is more general than ts,
     * then the resulting substitution refines the assumptions,
     * and it checks also if a quantor for a not quantifiable type variable
     * was claimed.
     *
     */
    public void specializeWith(HaskellObject ho,TypeSchema ts){
        this.delayedRefine();
        TypeSchema gts = this.pop();
        this.push(gts);
        TypeSchema nts = ts.getFreshCopy();
        Set<HaskellSym> wishQuans = new HashSet<HaskellSym>(nts.getQuantor());
        HaskellSubstitution subs = gts.match(nts,this.ccg);
        if (subs == null) {
            String info = "         "+gts+" II-->|>-- "+nts;
            HaskellSym.showee(new Apply(gts,nts));
            HaskellError.output(ho,info+"  infered type "+gts+"is not general enough for signature "+ts);
        } else {
            this.directRefine(subs);
            gts.setConstraints(Copy.deepCol(ts.getConstraints()));

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //HaskellError.println("    New: "+gts);
                //System.out.println("         "+gts+" AII-->>>-- "+nts);
            }

        }
        Set<HaskellSym> noQuans = this.noQuanStack.unitedGroups();
        /*
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("NQ:"+subs);
            System.out.println("NQ:"+noQuans);
            System.out.println("WQ:"+wishQuans);
        }
        */

        wishQuans.retainAll(noQuans);
        if (wishQuans.size()>0) {
           HaskellError.output(wishQuans.iterator().next(),"infered type "+gts+" is not general enough for signature "+ts);
        }
    }

    @Override
    public HaskellObject caseTypeExp(TypeExp ho){
        this.specializeWith(ho,ho.getTypeSchema());
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseModule(Module ho){
         return ho;
    }

    public HaskellObject forTerm(HaskellExp exp,Module module){
        this.setDefaultList(module.getDefaultList());
        exp.visit(this);

        TypeSchema ts = this.pop();

        Set<Set<ClassConstraint>> accss = ts.ambiguousConstraints(false);
        //this.solveAllAmbiguousConstraints(exp,accss);
        this.delayedRefine();
        this.reduce(ts.getConstraints());
        this.ccg.checkConstraints(ts.getConstraints(),exp);
        ts.autoQuantor();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println(exp +"::"+ts);
        }

        return ts;
    }

    public void forTuples(Modules modules){
        if (modules.getMainModule() != null){
            this.localGrouping(modules.getPrelude().getTupleGroups(),true);
        }
    }

    public void forModules(Modules modules){

        long totalTime = System.currentTimeMillis();

        this.forTuples(modules);
        List<Group> groups = modules.getGroups();
        this.localGrouping(groups,false);
        for(Group group :groups){
            this.setDefaultList(group.getGroupModule().getDefaultList());
            if ( (!group.isPreludeGroup()) && (!group.isAlreadyLoadedGroup()) ) {
                //System.err.println("**********************checkGroup:"+group);
                for(HaskellEntity e : group){
                    this.delayedRefine();
                    TypeSchema ts = this.assumptions.getTypeSchemaFor(e);
                    Set<Set<ClassConstraint>> accss = ts.ambiguousConstraints(false);
                    this.solveAllAmbiguousConstraints(e.getValue(),accss);
                    this.reduce(ts.getConstraints());
                    ts.autoQuantor();
                    this.assumptions.pushAssumption(e,ts);

                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        //System.out.println("Module ready " + e+ "::" + ts);
                    }

                }
            }
    }
        totalTime = System.currentTimeMillis() - totalTime;

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            System.err.println("totalTime: "+totalTime/1000.);
            System.err.println("forTimeSum: "+TypeInferenceVisitor.forTimeSum/1000.);
        }
    }

    @Override
    public void icaseLetExp(LetExp ho){
        List<Group> groups = ho.getGroups();
        this.push(TypeSchema.create(this.localGrouping(groups,false),Var.createFreshVar()));
    }

    @Override
    public HaskellObject caseLetExp(LetExp ho){
        this.delayedRefine();
        TypeSchema ts = this.pop();
        TypeSchema cs = this.pop();
        ts.getConstraints().addAll(cs.getConstraints());
        this.push(ts);
        return this.leave(ho);
    }

    @Override
    public void fcaseHaskellRule(HaskellRule ho){
        this.arguments.push(ho.getEntityFrame());
        this.noQuanStack.pushNewGroup();
        for (HaskellEntity e : ho.getEntityFrame().getCollectedEntities()){
            this.noQuanStack.addHoToPeekGroup(this.getAssumptionFor(e));
        }
        ho.getEntityFrame();
    }

    @Override
    public HaskellObject caseHaskellRule(HaskellRule ho){
        this.push(this.toArrow(ho.getPatterns().size()));
        this.arguments.pop();
        this.noQuanStack.popGroup();
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseEntity(HaskellEntity ho){
        return ho;
    }

    @Override
    public HaskellType buildArrow(HaskellType f,HaskellType x){
        return this.prelude.buildArrow(f,x);
    }

    @Override
    public TypeSchema getBoolTypeSchema(){
       return this.prelude.getBoolTypeSchema();
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){ // for substitution
        //this.extraAssumptions = walk(extraAssumptions,hv);
        //this.assumptions = walk(assumptions,hv);
        //this.tys = listWalk(tys,hv);
        super.visit(hv);
        for (Set<ClassConstraint> ccs : this.constraintStack){
            for (ClassConstraint cc : ccs){
                this.walk(cc,hv);
            }
        }
        for (HaskellObject ho : this.typeAnnos){
            ho.setTypeTerm(this.walk(ho.getTypeTerm(),hv));
        }
        return this;
    }

    public void directRefine(HaskellSubstitution subs){
        //HaskellError.println("Refine: "+subs);
        this.noQuanStack.apply(subs);
        this.visit(new VarSubstitutor(subs));


    }

    public void delayedRefine(){
        if (this.currentRefine != null) {
            this.directRefine(this.currentRefine);
            this.currentRefine = null;
        }
    }

    @Override
    public HaskellSubstitution refine(HaskellSubstitution subs){
        //this.directRefine(subs);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println(":: "+subs);
        }

        if (this.currentRefine != null) {
           this.currentRefine = this.currentRefine.combineWith(subs);
        } else {
           this.currentRefine = subs;
        }

        /*
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            HaskellError.println("Refine: "+subs);
        }

        VarSubstitutor vs = new VarSubstitutor(subs)
        this.visit();
        */

        return this.currentRefine;
    }


    @Override
    public void reduce(Set<ClassConstraint> cs){
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.print("[");
        }

        /*for (ClassConstraint c : cs){
           c.applyDirect(this.currentRefine);
        }*/

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("]");
        }

        this.ccg.reduce(cs);
    }

    @Override
    public HaskellObject leave(HaskellObject ho){
        this.typeAnnos.add(ho);
        ho.setTypeTerm(this.peek().getMatrix());
        return ho;
    }


    /**********************/

    @Override
    public boolean guardEntity(HaskellEntity ho){
        return true;
    }

    @Override
    public boolean guardEntities(Module ho) {
        return false;
    }

    @Override
    public boolean guardValue(HaskellEntity ho){
        return this.VALUESOF.contains(ho.getSort());
    }

    @Override
    public boolean guardLetFrame(LetExp ho){
        return false;
    }

    @Override
    public boolean guardType(HaskellEntity ho){
        return false;
    }

    @Override
    public boolean guardMember(HaskellEntity ho){
        return true;
    }

    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) {
        return false;
    }

    @Override
    public boolean guardDefType(SynTypeDecl ho){
        return false;
    }

    @Override
    public boolean guardConss(DataDecl ho){
        return false;
    }

    @Override
    public boolean guardTypeTypeExp(TypeExp ho) {
        return false;
    }

/*    public boolean guardPatDeclEntity(PatDeclValue ho) {
        return false;
    }*/

    @Override
    public boolean guardPatDecl(PatDecl ho)            {
        return false;
    }

}
