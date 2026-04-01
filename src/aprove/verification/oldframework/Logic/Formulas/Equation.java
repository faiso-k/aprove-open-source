package aprove.verification.oldframework.Logic.Formulas ;


import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.*;


/** an equation s == t.
 * @author  Burak, Eugen
 * @version $Id$
 */

public class Equation extends Formula implements PairOfTerms {

    protected AlgebraTerm left;
    protected AlgebraTerm right;

    private boolean flag;

    public Equation() {
        this.flag = false;
    }

    public void setFlag(boolean flag){
        this.flag = flag;
    }

    public boolean getFlag(){
        return this.flag;
    }

    // methods for the PairOfTerms interface
    //Accessors methods
    @Override
    public AlgebraTerm getLeft() {
        return this.left;
    }

    @Override
    public AlgebraTerm getRight() {
        return this.right;
    }

    public void setLeft( AlgebraTerm left ) {
        this.left = left;
    }
    public void setRight( AlgebraTerm right ) {
        this.right = right;
    }

     /**
      *
      * @param ev
      * @return true if ev can evaluate this equation
      */
    @Override
    public boolean evaluable(Evaluator ev){
        if (this.left.evaluable(ev) || this.right.evaluable(ev) ) {
            return true;
        }

        if (this.left.getSymbol() instanceof ConstructorSymbol && this.right.getSymbol()  instanceof ConstructorSymbol) {
            return true;
        }

        if (this.left.equals(this.right)) {
            return true;
        }
        return false;
    }

    @Override
    public Formula deepcopy(){
        Equation newFormula = Equation.create(this.left.deepcopy(), this.right.deepcopy());
        newFormula.setFlag(this.flag);
        return newFormula;
    }

    @Override
    public Formula shallowcopy(){
      return Equation.create(this.left.deepcopy(), this.right.deepcopy());
    }

    // creation, visitor methods

    protected Equation( AlgebraTerm left, AlgebraTerm right) {
        this.left  = left;
        this.right = right;
    }

    public static Equation create( AlgebraTerm s, AlgebraTerm t) {
        return new Equation(s, t);
    }

    public static Equation create( PairOfTerms p ) {
        return new Equation( p.getLeft(), p.getRight());
    }

    @Override
    public <T> T apply( FineFormulaVisitor<T> fv ) {

    return fv.caseEquation( this );
    }

    @Override
    public <T> T apply( CoarseFormulaVisitor<T> cfv ) {
    return cfv.caseEquation( this );
    }


    @Override
    public <T> T apply(CoarseFormulaVisitorException<T> cfve) throws InvalidPositionException {
        return cfve.caseEquation(this);
    }

    @Override
    public <T> T apply(FineFormulaVisitorException<T> fve) throws InvalidPositionException {
        return fve.caseEquation(this);
    }

    @Override
    public boolean equals(Object object) {

        if( object instanceof Equation ) {
            Equation equation = (Equation)object;
            return this.getAsRepresentationSet().equals(equation.getAsRepresentationSet());
        } else {

            return false;

        }

    }

    public AlgebraTerm asTermEquation(Program program) {

        AlgebraTerm typeTerm  =  program.getTypeContext().typeCheck( new FreshVarGenerator(),TypeTools.equi(this.left, this.right));

        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(this.left);
        args.add(this.right);

        System.out.println(TypeTools.getResultTerm(typeTerm));

        return DefFunctionApp.create(program.getPredefFunctionSymbol("equal_" +
                TypeTools.getResultTerm( typeTerm )), args);
    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexEquationSymbol();
    }

    @Override
    public boolean isAtomic() {
        return true;
    }

    @Override
    public boolean isEquation() {
        return true;
    }

    @Override
    public boolean isImplication() {
        return false;
    }

    @Override
    public List<AlgebraTerm> getArguments() {

        List<AlgebraTerm> returnValue = new Vector<AlgebraTerm>();
        returnValue.add(this.getLeft());
        returnValue.add(this.getRight());

        return returnValue;
    }

    public Set<AlgebraTerm> getAsRepresentationSet() {
        Set<AlgebraTerm> set = new LinkedHashSet<AlgebraTerm>();
        set.add(this.left);
        set.add(this.right);
        return set;
    }

    @Override
    public AlgebraSubstitution matchesWithIdentities(Formula that, AlgebraSubstitution subs) throws UnificationException {

        if(!(that instanceof Equation)) {
            throw new MatchFailureException("match failure",null,null);
        }

        AlgebraSubstitution substitution = this.left.matchesWithIdentities(((Equation)that).getLeft(), subs);
        return this.right.matchesWithIdentities(((Equation)that).getRight(),substitution) ;
    }

}
