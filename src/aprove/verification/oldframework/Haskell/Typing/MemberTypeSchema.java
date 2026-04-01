package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The MemberTypeSchema is the TypeSchema for class entities, cause
 * the have an extra implicit class constraint.
 */

public class MemberTypeSchema extends TypeSchema implements HaskellBean {
    ClassConstraint classConstraint;

    /**
     * do not use this constructor, its only for bean convention
     */
    public MemberTypeSchema(){
    }

    /**
     * normal constructor
     */
    public MemberTypeSchema(ClassConstraint classConstraint,Quantor quantor, Set<ClassConstraint> constraints,HaskellType matrix){
        super(quantor,constraints,matrix);
        this.classConstraint = classConstraint;
    }

    public ClassConstraint getClassConstraint(){
        return this.classConstraint;
    }

    public void setClassConstraint(ClassConstraint classConstraint){
        this.classConstraint = classConstraint;
    }

    @Override
    public Object deepcopy(){
        ClassConstraint mcc = null;
        Set<ClassConstraint> nccs = new HashSet<ClassConstraint>();
        for (ClassConstraint cc : this.constraints){
            ClassConstraint ncc = Copy.deep(cc);
            if (cc == this.classConstraint) { mcc = ncc; }
            nccs.add(ncc);
        }
        if (mcc == null) {
            mcc = Copy.deep(this.classConstraint);
        }
        return new MemberTypeSchema(mcc,Copy.deep(this.quantor),nccs,Copy.deep(this.matrix));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseTypeSchema(this);
        this.quantor = this.walk(this.quantor,hv);
        this.constraints = this.listWalk(this.constraints,hv);
        if (hv.guardMemberTypeSchemaClassConstraint(this)){
           this.classConstraint = this.walk(this.classConstraint,hv);
        }
        this.matrix = this.walk(this.matrix,hv);
        return hv.caseTypeSchema(this);
    }

    @Override
    public String toString(){
        return "Member: "+this.classConstraint+" m "+super.toString();
    }

    /**
     * @param instance the instance for the class type variable
     * @return a TypeSchema which contains all constraint of this MemberTypeSchema,
     *         but the implicit class constraint is removed, and the class instance varibale
     *         is replaced by the instance.
     */
    public TypeSchema instantiate(TypeSchema instance){
        TypeSchema fi = instance.getFreshInstance();

        HaskellType nMatrix = Copy.deep(this.matrix);
        Set<ClassConstraint> nConstraints = Copy.deepCol(this.constraints);
        nConstraints.remove(this.classConstraint);
        nConstraints.addAll(fi.getConstraints());

        TypeSchema ts = TypeSchema.create(nConstraints,nMatrix);
        HaskellSubstitution subs = new HaskellSubstitution((Var)this.classConstraint.getType(),fi.getMatrix());
        ts.visit(new VarSubstitutor(subs));
        ts.autoQuantor();
        return ts;
    }
}
