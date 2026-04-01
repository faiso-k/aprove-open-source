package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public abstract class OmegaVisitor extends HaskellVisitor {
    public Assumptions assumptions;
    public Assumptions extraAssumptions;
    public Stack<TypeSchema> tys;
    public Prelude prelude;

    public OmegaVisitor(Assumptions assumptions,Prelude prelude){
        this.prelude = prelude;
        this.assumptions = assumptions;
        this.tys = new Stack<TypeSchema>();
    }

    public void resetStack(){
        this.tys = new Stack<TypeSchema>();
    }

    public Assumptions getAssumptions(){
        return this.assumptions;
    }

    public void setExtraAssumptions(Assumptions extraAssumptions){
        this.extraAssumptions = extraAssumptions;
    }

    public void push(TypeSchema ts){
        this.tys.push(ts);
    }

    public TypeSchema peek(){
        return this.tys.peek();
    }

    public TypeSchema pop(){
        return this.tys.pop();
    }

    public TypeSchema getTypeSchema(HaskellEntity e){
       TypeSchema ty = this.assumptions.getTypeSchemaFor(e);
       if (ty == null) {
           ty = TypeSchema.create(Var.createFreshVar());
           this.assumptions.pushAssumption(e,ty);
       }
       return ty.getFreshInstance();
    }

    @Override
    public void fcaseAtom(Atom ho){
       // XXX DEBUG
       if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
           //System.out.println("Omega Visitor:"+ho.getSymbol()+","+ho.getSymbol().getEntity()+","+ho.getSymbol().getClass());
       }

       this.push(this.getTypeSchema(ho.getSymbol().getEntity()));
       this.leave(ho);
    }

    @Override
    public HaskellObject caseJokerPat(JokerPat ho){
       this.push(TypeSchema.create(Var.createFreshVar()));
       return this.leave(ho);
    }

    @Override
    public HaskellObject caseApply(Apply ho){
        TypeSchema tyforx = this.pop();
        TypeSchema tyforf = this.pop();
        Var nvar = Var.createFreshVar();
        HaskellType ty = this.buildArrow(tyforx.getMatrix(),nvar);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("!!tyforf:"+tyforf);
            //System.out.println("!!tyforx:"+tyforx);
            /*HaskellError.output = true;
            HaskellError.println(ho.hashCode()+" Apply Function: "+ho.getFunction()+" :: "+tyforf);
            HaskellError.println(ho.hashCode()+" Apply Value:    "+ho.getArgument()+" :: "+tyforx);
            HaskellError.println(ho.hashCode()+" Apply mgu("+tyforf.getMatrix().toString()+","+ty.toString()+")");*/
        }

        HaskellSubstitution subs = this.refine(this.mguWithCC(tyforf.getConstraints(),tyforf.getMatrix(),tyforx.getConstraints(),ty,ho));

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
    //        HaskellError.println("="+subs);
            //Show.Me("mgu").add("subs",subs).add("forf",forf).add("forx",forx).add("nvar",nvar).show();

            //HaskellError.println(ho.hashCode()+" Apply refined Function: "+tyforf);
            //HaskellError.println(ho.hashCode()+" Apply refined Value:    "+tyforx);
        }

        HaskellType ntype = (HaskellType) subs.applyTo(nvar);
        Set<ClassConstraint> coJ = this.coJoin(tyforf,tyforx,subs);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //HaskellError.println(ho.hashCode()+" Apply CoJoin:"+coJ);
        }

        TypeSchema res = this.reduceConstraints(coJ,ntype);
        this.push(res);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //HaskellError.println(ho.hashCode()+" Apply Result:"+res);
            //System.out.println("!!res:"+res);
        }

        return this.leave(ho);
    }

    @Override
    public HaskellObject caseLambdaExp(LambdaExp ho){
        TypeSchema ts = this.toArrow(ho.getPatterns().size());
        this.push(ts);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("Lambda ts: "+ts); HaskellError.output = true;
        }

        return this.leave(ho);
    }

    @Override
    public HaskellObject caseAltExp(AltExp ho){
        TypeSchema pts = this.pop();
        TypeSchema rts = this.pop();
        this.push(rts);
        this.push(pts);
        //HaskellError.println("Pts: "+pts);
        //HaskellError.println("Rts: "+rts);
        TypeSchema ts = this.toArrow(1);
        this.push(ts);
        //HaskellError.println("AltExpType: "+ts);
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseCaseExp(CaseExp ho){
        TypeSchema altTs = this.massMgu(ho.getCases().size(),ho);
        TypeSchema argTs = this.pop();
        Var nVar = Var.createFreshVar();
        this.push(TypeSchema.create(nVar));
        this.push(argTs);
        this.push(TypeSchema.create(nVar));
        this.push(this.toArrow(1)); // Stack: nVar , argTS->nVar,  altTs
        this.push(altTs);
        this.push(this.addConstraintsFromTo(this.massMgu(2,ho),this.pop())); // mgu (argTs->nVar, altTs)
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseHaskellRule(HaskellRule ho){
        this.push(this.toArrow(ho.getPatterns().size()));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseFunction(Function ho){
        //HaskellError.println("Stack " +this.tys.size()+" >= "+ho.getRules().size());
        this.push(this.massMgu(ho.getRules().size(),ho));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseCondExp(CondExp ho){
        TypeSchema resTs = this.pop();
        this.push(this.getBoolTypeSchema());
        this.push(this.addConstraintsFromTo(this.massMgu(2,ho),resTs));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseIfExp(IfExp ho){
        TypeSchema resTs = this.massMgu(2,ho);
        this.push(this.getBoolTypeSchema());
        this.push(this.addConstraintsFromTo(this.massMgu(2,ho),resTs));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseCondStackExp(CondStackExp ho){
        this.push(this.massMgu(ho.getConditions().size(),ho));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseBindPat(BindPat ho){
        this.push(this.massMgu(2,ho));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseIrrPat(IrrPat ho){
        return this.leave(ho);
    }

    @Override
    public HaskellObject casePatDecl(PatDecl ho) {
        //this.push(this.massMgu(2,ho));
        return this.leave(ho);
    }

    @Override
    public HaskellObject caseSynTypeDecl(SynTypeDecl ho) {
        this.push(this.massMgu(2,ho));
        return this.leave(ho);
    }


    public TypeSchema massMgu(int j,HaskellObject ho){
        TypeSchema cur = this.pop();
        for (int i=1;i<j;i++){
            TypeSchema ts = this.pop();
            HaskellSubstitution subs = this.refine(this.mguWithCC(cur.getConstraints(),cur.getMatrix(),ts.getConstraints(),ts.getMatrix(),ho));

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("!!massmguA:"+cur);
                //System.out.println("!!massmguB:"+ts);
               // HaskellError.println("Mass mgu("+cur.getMatrix().toString()+","+ts.getMatrix().toString()+")");
                //HaskellError.println("="+subs);
            }

            HaskellType ntype = (HaskellType) subs.applyTo(cur.getMatrix());
            cur = this.reduceConstraints(this.coJoin(cur,ts,subs),ntype);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("!!=massmgu:"+cur);
            }
        }
        return cur;
    }

    public TypeSchema toArrow(int j) {
        TypeSchema cur = this.pop();
        for (int i=0;i<j;i++){
            TypeSchema ts = this.pop();
            cur = this.reduceConstraints(this.coJoin(cur,ts,null),this.buildArrow(ts.getMatrix(),cur.getMatrix()));
        }
        return cur;
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){ // for substitution
        this.extraAssumptions = this.walk(this.extraAssumptions,hv);
        this.assumptions = this.walk(this.assumptions,hv);
        this.tys = this.listWalk(this.tys,hv);
        return this;
    }

    public HaskellSubstitution refine(HaskellSubstitution subs){
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            HaskellError.println("Refine: "+subs);
            //System.out.println("Refine ");
        }

        this.visit(new VarSubstitutor(subs));
        return subs;
    }

    public Set<ClassConstraint> coJoin(TypeSchema a,TypeSchema b,HaskellSubstitution subs){
        Set<ClassConstraint> res = new HashSet<ClassConstraint>();
        for (ClassConstraint c : a.getConstraints()){
            res.add(c.apply(subs));
        }
        for (ClassConstraint c : b.getConstraints()){
            res.add(c.apply(subs));
        }
        return res;
    }


    public TypeSchema addConstraintsFromTo(TypeSchema a,TypeSchema b){
        Set<ClassConstraint> ccs = this.coJoin(a,b,new HaskellSubstitution());
        return TypeSchema.create(ccs,b.getMatrix());
    }

    public TypeSchema reduceConstraints(Set<ClassConstraint> cs,HaskellType matrix){
        this.reduce(cs);
        return TypeSchema.create(cs,matrix);
    }

    public abstract HaskellType buildArrow(HaskellType f,HaskellType x);
    public abstract HaskellSubstitution mgu(BasicTerm a,BasicTerm b,HaskellObject ho);

    public void reduce(Set <ClassConstraint> cs){
    }

    public HaskellObject leave(HaskellObject ho){
        return ho;
    }

    public TypeSchema getBoolTypeSchema(){
       return null;
    }

    public HaskellSubstitution mguWithCC(Set<ClassConstraint> cas,HaskellType a,Set<ClassConstraint> cbs, HaskellType b,HaskellObject ho){
        return this.mgu(a,b,ho);
    }
}
