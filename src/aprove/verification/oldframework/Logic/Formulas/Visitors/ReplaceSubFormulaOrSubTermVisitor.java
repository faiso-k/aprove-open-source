/*
 * Created on 28.10.2004
 */
package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * @author rabe
 */
public class ReplaceSubFormulaOrSubTermVisitor implements CoarseGrainedTermVisitorException<TermOrFormula>,
    CoarseFormulaVisitorException<TermOrFormula> {

    protected Position positionToReplace;

    protected TermOrFormula   newSubPart;

    protected Stack<Position> stackOfCurrentPosition;

    protected Stack<TermOrFormula>   stackOfSubParts;

    public static Formula apply(Formula formula, AlgebraTerm term, Position position)
            throws InvalidPositionException {
        ReplaceSubFormulaOrSubTermVisitor thisVisitor = new ReplaceSubFormulaOrSubTermVisitor(term, position);
        return (Formula)formula.apply(thisVisitor);
    }

    public static Formula apply(Formula formula, Formula nformula, Position position)
            throws InvalidPositionException{
        ReplaceSubFormulaOrSubTermVisitor thisVisitor = new ReplaceSubFormulaOrSubTermVisitor(nformula,position);
        return (Formula)formula.apply(thisVisitor);
    }

    protected ReplaceSubFormulaOrSubTermVisitor(TermOrFormula subPart, Position position) {
        this.positionToReplace       = position;
        this.newSubPart              = subPart;
        this.stackOfCurrentPosition  = new Stack<Position>();
        this.stackOfSubParts         = new Stack<TermOrFormula>();

        this.stackOfCurrentPosition.push(Position.create());
    }

    @Override
    public TermOrFormula caseVariable(AlgebraVariable v) throws InvalidPositionException {

        Position position = this.stackOfCurrentPosition.pop();

        if(position.equals(this.positionToReplace)) {

            if( this.newSubPart.isTerm()) {
                this.stackOfSubParts.push(((AlgebraTerm)this.newSubPart).deepcopy());
            } else {
                throw new InvalidPositionException(position,"Expected Term");
            }

        } else {
            this.stackOfSubParts.push(v.deepcopy());
        }

        return this.stackOfSubParts.peek();
    }

    @Override
    public TermOrFormula caseFunctionApp(AlgebraFunctionApplication f)
            throws InvalidPositionException {

        Position position = this.stackOfCurrentPosition.pop();

        if( position.equals(this.positionToReplace) ) {
            if( this.newSubPart.isTerm()) {
                this.stackOfSubParts.push(((AlgebraTerm)this.newSubPart).deepcopy());
                return null;
            } else {
                throw new InvalidPositionException(position,"Expected Term");
            }
        }

        List<AlgebraTerm> arguments = f.getArguments();

        for(int i=0; i < arguments.size(); i++){

            Position newPosition = position.shallowcopy();
            newPosition.add(i);
            this.stackOfCurrentPosition.push(newPosition);

            arguments.get(i).apply(this);

        }

        LinkedList<AlgebraTerm> newArguments = new LinkedList<AlgebraTerm>();

        for(int i=0; i < arguments.size(); i++){
            newArguments.addFirst((AlgebraTerm)this.stackOfSubParts.pop());
        }

        this.stackOfSubParts.push( AlgebraFunctionApplication.create(f.getFunctionSymbol(), newArguments));

        return this.stackOfSubParts.peek();
    }

    @Override
    public TermOrFormula caseTruthValue(FormulaTruthValue truthvalFormula) throws InvalidPositionException {

        Position position = this.stackOfCurrentPosition.pop();

        if( position.equals(this.positionToReplace)) {

            if( this.newSubPart.isFormula()) {
                this.stackOfSubParts.push(((Formula)this.newSubPart).deepcopy());
            } else {
                throw new InvalidPositionException(position,"Expected Formula");
            }
        } else {
            this.stackOfSubParts.push(truthvalFormula.deepcopy());
        }

        return this.stackOfSubParts.peek();
    }

    @Override
    public TermOrFormula caseEquation(Equation eqFormula)
            throws InvalidPositionException {

        Position position = this.stackOfCurrentPosition.pop();

        if( position.equals(this.positionToReplace) ) {
            if( this.newSubPart.isFormula()) {
                this.stackOfSubParts.push( ((Formula)this.newSubPart).deepcopy());
                return this.stackOfSubParts.peek();
            }
        }

        Position newPosition = position.shallowcopy();
        newPosition.add(0);
        this.stackOfCurrentPosition.push(newPosition);

        eqFormula.getLeft().apply(this);

        newPosition = position.shallowcopy();
        newPosition.add(1);
        this.stackOfCurrentPosition.add(newPosition);

        eqFormula.getRight().apply(this);

        AlgebraTerm rightTerm = (AlgebraTerm)this.stackOfSubParts.pop();
        AlgebraTerm leftTerm  = (AlgebraTerm)this.stackOfSubParts.pop();

        this.stackOfSubParts.push( Equation.create( leftTerm ,rightTerm));

        return this.stackOfSubParts.peek();
    }

    @Override
    public TermOrFormula caseJunctorFormula(JunctorFormula jFormula)
            throws InvalidPositionException {

        Position position = this.stackOfCurrentPosition.pop();

        if( position.equals(this.positionToReplace)) {

            if(this.newSubPart.isFormula()) {
                this.stackOfSubParts.push(((Formula)this.newSubPart).deepcopy());
                return this.stackOfSubParts.peek();
            }else{
                throw new InvalidPositionException(position,"Expected Formula");
            }

        }

        Position newPosition = position.shallowcopy();
        newPosition.add(0);
        this.stackOfCurrentPosition.push(newPosition);

        jFormula.getLeft().apply(this);

        if( !(jFormula instanceof Not) ) {

            newPosition = position.shallowcopy();
            newPosition.add(1);
            this.stackOfCurrentPosition.push(newPosition);
            jFormula.getRight().apply(this);

        }

        if( jFormula instanceof Not) {

            this.stackOfSubParts.push( Not.create((Formula)this.stackOfSubParts.pop()));

        } else {

            Formula rightFormula = (Formula)this.stackOfSubParts.pop();
            Formula leftFormula     = (Formula)this.stackOfSubParts.pop();


            if (jFormula instanceof And) {
                this.stackOfSubParts.push( And.create(leftFormula,rightFormula));
            }

            if (jFormula instanceof Or) {
                this.stackOfSubParts.push( Or.create(leftFormula,rightFormula));
            }

            if (jFormula instanceof Implication) {
                this.stackOfSubParts.push( Implication.create(leftFormula,rightFormula));
            }

            if (jFormula instanceof Equivalence) {
                this.stackOfSubParts.push( Equivalence.create(leftFormula,rightFormula));
            }
        }
        return this.stackOfSubParts.peek();
    }

}
