package aprove.verification.oldframework.Typing;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A type represent a haskell-like polymorphic type scheme
 * with a type matrix and a type quantifier.
 * @author Stephan Swiderski
 * @version $Id$
 */

public class Type implements java.io.Serializable {
    protected TypeQuantifier typeQuantifier;      // Quantified variables
    protected AlgebraTerm typeMatrix;          // the type matrix as term

    public Type() {
        this.typeQuantifier = null;
        this.typeMatrix = null;
    }
    /**
     * Creates a new Type by using a quantifier and a type matrix.
     * Modifing this new type will change the given type matrix and
     * quantifier.
     * @param quan the quantifier (no deepcopy)
     * @param typeMatrix the typematrix (no deepcopy)
     */
    public Type(TypeQuantifier quan, AlgebraTerm typeMatrix) {
        this.typeMatrix = typeMatrix;
        this.typeQuantifier = quan;
    }

    /**
     * Creates a new Type with a empty new quantifier by using a type matrix.
     * Modifing this new type will change the given type matrix.
     * @param typeMatrix the typematrix (no deepcopy)
     */
    public Type(AlgebraTerm typeMatrix) {
        this.typeMatrix = typeMatrix;
        this.typeQuantifier = new TypeQuantifier();
    }

    /**
     * Returns a deep copy of this type, i.e. a type that has the
     * same structure and uses the same symbols (of current {@link TypeContext}).
     * Note: Changing the symbols will result in changes to the
     * original type.
     */
    public Type deepcopy(){
        return new Type(this.typeQuantifier.deepcopy(),this.typeMatrix.deepcopy());
    }

    /**
     * Only applies a term visitor to the typeMatrix, not to the quantifiers
     */
    public void applyToMatrix(CoarseGrainedTermVisitor vis){
        this.typeMatrix = (AlgebraTerm) this.typeMatrix.apply(vis);
    }

    /**
     * Only applies a substitution to the typeMatrix, not to the quantifiers
     * this current type will change.
     */
    public void applyToMatrix(AlgebraSubstitution subs){
        this.typeMatrix = (AlgebraTerm) this.typeMatrix.apply(subs);
    }

    /**
     * Returns the type quantifier of this type (changes will change the type).
     * @return type quantifier as term
     */
    public TypeQuantifier getTypeQuantifier(){
        return this.typeQuantifier;
    }

    /**
     * Returns the type matrix of this type (changes will change the type).
     * @return type matrix as term
     */
    public AlgebraTerm getTypeMatrix(){
        return this.typeMatrix;
    }

    /**
     * Returns the free (only unquantified) variables of this type.
     * @return free varibales
     */
    public Set<AlgebraVariable> getFreeVars(){
       Set<AlgebraVariable> sov = this.typeMatrix.getVars();
       sov.removeAll(this.typeQuantifier);
       return sov;
    }

    /**
     * Generates a fresh type term as an instance of this type.
     * The instance is a copy of the type matrix,
     * but the quantified variables are renamed in fresh ones.
     * @param fvg fresh var generator cause of possible renamings
     * @return type term with renamed variables
     */
    public AlgebraTerm getFreshInstance(FreshVarGenerator fvg){
        return this.typeMatrix.apply(this.typeQuantifier.freshVarRename(fvg));
    }

    /**
     * construct the type of for selector out of a type
     * @param i the index of the argument for creating the selector for
     * @return the type of this selector
     */
    public Type createSelType(int i){
        AlgebraTerm tau = this.getTypeMatrix();
        AlgebraTerm a = TypeTools.getFunctionArgAt(tau,i);
    AlgebraTerm b = TypeTools.getResultTerm(tau);
    List<AlgebraTerm> bs = new Vector<AlgebraTerm>();
        bs.add(b);
    return TypeTools.autoQuan(TypeTools.function(bs,a));
    }

    /**
     * Generates all positions in which this function-type is reflexive
     * w.r.t. the output type term of this type
     * <code>(t1,...,tn) -> ti </code> this type is reflexive in position i
     * <code>(a,a,a) -> (a -> a)</code> this type is reflexive in positions 00 01 02 10
     * (cause the term at position 11 ist the output type term)
     * @return a set of postions in which the function symbol of this type is reflexive
     */
    public Set<Position> reflexivePositions(){
       Set<Position> sop = new HashSet<Position>();
       Position p = Position.create();
       List<AlgebraTerm> lot = TypeTools.getArrowTerms(this.typeMatrix);
       int len = lot.size()-1;
       AlgebraTerm mt = (AlgebraTerm) lot.get(len); // last term is match term
       //System.out.println(">" + mt.toString());
       for (int i=0;i<len;i++){
           AlgebraTerm t = (AlgebraTerm) lot.get(i);
           //System.out.println("-" + t.toString());
       Position cp = p.shallowcopy();
       if (len>1) { cp.add(0); }
       t.apply(new GetTermPositionsVisitor(cp,mt,sop));
       p.add(1);
       }
       return sop;
    }

    /**
     * Checks if a function symbol of this type is reflexive.
     * @return true if reflexive, otherwise false;
     */
    public boolean isReflexive(){
       List<AlgebraTerm> lot = TypeTools.getArrowTerms(this.typeMatrix);
       int len = lot.size()-1;
       AlgebraTerm mt = (AlgebraTerm) lot.get(len); // last term is match term
       for (int i=0;i<len;i++){
           AlgebraTerm t = (AlgebraTerm) lot.get(i);
       Boolean b = (Boolean) t.apply(new ContainsTermVisitor(mt));
       if (b.booleanValue()) { return true; }
       }
       return false;
    }

    /**
     * Generates a string like this <code><q1,...,qn>tau</code>
     * @return String <code>"<q1,..qn>tau"</code>
     */
    @Override
    public String toString(){
       return this.typeQuantifier.toString()+this.typeMatrix.toString();
    }

    public void setTypeMatrix(AlgebraTerm typeMatrix) {
        this.typeMatrix = typeMatrix;
    }

    public void setTypeQuantifier(TypeQuantifier typeQuantifier) {
        this.typeQuantifier = typeQuantifier;
    }

    @Override
    public int hashCode() {
        return this.typeMatrix.toString().hashCode();
    }

    @Override
    public boolean equals(Object that) {

        if( that instanceof Type) {
            Type thatType = (Type)that;
            return this.typeMatrix.equals(thatType.typeMatrix) && this.typeQuantifier.equals(thatType.typeQuantifier);
        }
        return false;
    }

}
