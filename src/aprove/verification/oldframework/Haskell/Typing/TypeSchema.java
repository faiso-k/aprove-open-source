package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class TypeSchema extends HaskellObject.Visitable {
    Quantor quantor;
    Set<ClassConstraint> constraints;
    HaskellType matrix;

    /**
     * do not use this constructor, its only for bean convention
     */
    public TypeSchema(){
    }

    /**
     * constructor for deepcopy
     */
    public TypeSchema(Quantor quantor, Set<ClassConstraint> constraints,HaskellType matrix){
        this.quantor = quantor;
        this.constraints = constraints;
        this.matrix = matrix;
    }

    public void setQuantor(Quantor quantor){
        this.quantor = quantor;
    }

    public Quantor getQuantor(){
        return this.quantor;
    }

    public Set<ClassConstraint> getConstraints(){
        return this.constraints;
    }
    public void setConstraints(Set<ClassConstraint> constraints){
        this.constraints = constraints;
    }

    public void addConstraints(Set<ClassConstraint> ccs){
        this.constraints.addAll(ccs);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new TypeSchema(Copy.deep(this.quantor),Copy.deepCol(this.constraints),Copy.deep(this.matrix)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseTypeSchema(this);
        this.quantor = this.walk(this.quantor,hv);
        this.constraints = this.listWalk(this.constraints,hv);
        this.matrix = this.walk(this.matrix,hv);
        return hv.caseTypeSchema(this);
    }

    public HaskellType getMatrix(){
        return this.matrix;
    }

    public void setMatrix(HaskellType matrix){
        this.matrix = matrix;
    }

    /**
     * deepcopy of this typeschema with Symbol renaming (so all variables have new fresh symbols)
     */
    public TypeSchema getFreshCopy(){
        return this.walk(Copy.deep(this),new VarSubstitutor(new HaskellSubstitution(this.quantor)));
    }

    /**
     * @returns a new typeschema (changes to that,have no influence on this typeschema)
     *          which is a new fresh instance (new variables) of this typeschema
     */
    public TypeSchema getFreshInstance(){
        HaskellType nMatrix = Copy.deep(this.matrix);
        Set<ClassConstraint> nConstraints = Copy.deepCol(this.constraints);
        TypeSchema nts = TypeSchema.create(nConstraints,nMatrix);
        return this.walk(nts,new VarSubstitutor(new HaskellSubstitution(this.quantor)));
    }

    /**
     * @returns a set of HaskellSym's of variables which occur in the constraints of this typeschema
     */
    public Set<HaskellSym> getConstrainedSyms(){
        Set<HaskellSym> syms = new HashSet<HaskellSym>();
        FreeVarSymCollector fvsc = new FreeVarSymCollector(syms);
        this.constraints = this.listWalk(this.constraints,fvsc);
        syms.removeAll(this.quantor);
        return syms;
    }

    /**
     * adds variables occuring in the matrix to the quantor of this typeschema
     * if they does not occur in noQuans
     */
    public boolean autoQuantor(Set<HaskellSym> noQuans){
        this.autoQuantor();
        return this.quantor.removeAll(noQuans);
    }

    /**
     * adds all variables occuring in the matrix to the quantor
     */
    public void autoQuantor(){
        this.quantor = null;
        Quantor nQuantor = new Quantor();
        FreeVarSymCollector fvsc = new FreeVarSymCollector(nQuantor);
        this.visit(fvsc);
        this.quantor = nQuantor;
    }

    /**
     * static constructor
     */
    public static TypeSchema create(Set<ClassConstraint> constraints,HaskellType matrix){
        return new TypeSchema(new Quantor(),constraints,matrix);
    }

    /**
     * static constructor
     */
    public static TypeSchema create(HaskellType matrix){
        return new TypeSchema(new Quantor(),new HashSet<ClassConstraint>(),matrix);
    }

    @Override
    public String toString(){
        return this.quantor+"--"+this.constraints+"--"+this.matrix;
    }

    /**
     * @returns non-null-Substitution,iff this*subs = ts
     */
    public HaskellSubstitution match(TypeSchema ts,ClassConstraintGraph ccg){
        HaskellSubstitution subs = BasicTerm.Tools.match(this.getMatrix(),ts.getMatrix());
        if (subs == null) {
            return null;
        }
        HaskellError.println(" pre ts-match: "+subs);
        /*Set<HaskellSym> genSyms = new HashSet<HaskellSym>();
        FreeVarSymCollector fvsc = new FreeVarSymCollector(genSyms);*/
        Set<ClassConstraint> sccs = ccg.matrixReduce(Copy.deepCol(ts.getConstraints()),ts.getMatrix());
        Set<ClassConstraint> ccs = new HashSet<ClassConstraint>();
        for (ClassConstraint cc : ccg.matrixReduce(this.getConstraints(),this.getMatrix())) {
            ccs.add(cc.apply(subs));
        }
        ccg.reduce(ccs);
        ccg.reduce(sccs);
        if (!ccg.moreGeneralThan(ccs,sccs)) {
            HaskellError.println("Reduced sccs:"+sccs);
            HaskellError.println("Reduced ccs:"+ccs);
            return null;
        }
        HaskellError.println(" ts-match: "+subs);
        return subs;
    }

    /**
     * returns a set of class constraint sets each of these sets
     * contains class constraints which share the same type variable
     */
    public Set<Set<ClassConstraint>> ambiguousConstraints(boolean matrixBoundFilter){
        Set<Set<ClassConstraint>> res = new HashSet<Set<ClassConstraint>>();
        Set<HaskellSym> syms = new HashSet<HaskellSym>();
        Set<HaskellSym> fsyms = new HashSet<HaskellSym>();
        FreeVarSymCollector ccfvsc = new FreeVarSymCollector(fsyms);
        for (ClassConstraint cc : this.getConstraints()){
            cc.visit(ccfvsc);
        }
        if (matrixBoundFilter){
            FreeVarSymCollector fvsc = new FreeVarSymCollector(syms);
            this.matrix.visit(fvsc);
            fsyms.removeAll(syms);
        } else {
            fsyms.removeAll(this.quantor);
        }
        for (HaskellSym sym : fsyms){
            Set<ClassConstraint> cres = new HashSet<ClassConstraint>();
            for (ClassConstraint cc : this.getConstraints()){
               Set<HaskellSym> csyms = new HashSet<HaskellSym>();
               FreeVarSymCollector cfvsc = new FreeVarSymCollector(csyms);
               cc.visit(cfvsc);
               if (csyms.contains(sym)) {
                   cres.add(cc);
               }
            }
            if (cres.size()>0) {
                res.add(cres);
            }
        }
        return res;
    }
}
