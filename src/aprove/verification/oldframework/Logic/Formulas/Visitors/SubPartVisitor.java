/*
 * Created on 29.10.2004
 */
package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * @author rabe
 */
public class SubPartVisitor implements CoarseFormulaVisitor<TermOrFormula>, CoarseGrainedTermVisitor<TermOrFormula> {

    protected Position positionToReturn;

    protected Stack<Position> stackOfCurrentPosition;

    public static TermOrFormula apply(TermOrFormula termOrFormula, Position position) throws InvalidPositionException{

        SubPartVisitor thisVisitor = new SubPartVisitor(position);

        try {
        if( termOrFormula.isFormula() ) {
            return ((Formula)termOrFormula).apply(thisVisitor);
        }else{
            return ((AlgebraTerm)termOrFormula).apply(thisVisitor);
        }
        }catch(Exception e) {
            System.out.println("ARG:"+termOrFormula+","+position);
            return null;
        }

    }

    protected SubPartVisitor(Position position) {
        this.positionToReturn = position;

        this.stackOfCurrentPosition  = new Stack<Position>();
        this.stackOfCurrentPosition.push(Position.create());
    }

    @Override
    public TermOrFormula caseVariable(AlgebraVariable v) {

        Position position;

        position = this.stackOfCurrentPosition.pop();

        if(position.equals(this.positionToReturn)) {

            return v.deepcopy();

        }

        return null;
    }

    @Override
    public TermOrFormula caseFunctionApp(AlgebraFunctionApplication f) {

        Position position;

        position = this.stackOfCurrentPosition.pop();

        if( position.equals(this.positionToReturn) ) {
            return f.deepcopy();
        }

        List<AlgebraTerm> arguments = f.getArguments();

        for(int i=0; i < arguments.size(); i++){

            Position newPosition = position.shallowcopy();
            newPosition.add(i);
            this.stackOfCurrentPosition.push(newPosition);

            TermOrFormula returnValue = arguments.get(i).apply(this);

            if( returnValue != null ) {
                return returnValue;
            }

        }

        return null;
    }

    @Override
    public TermOrFormula caseTruthValue(FormulaTruthValue truthvalFormula) {

        Position position = this.stackOfCurrentPosition.pop();

        if( position.equals(this.positionToReturn)) {
            return truthvalFormula.deepcopy();
        }

        return null;
    }

    @Override
    public TermOrFormula caseEquation(Equation eqFormula) {

        Position position = this.stackOfCurrentPosition.pop();

        if( position.equals(this.positionToReturn) ) {
            return eqFormula.deepcopy();
        }

        Position newPosition = position.shallowcopy();
        newPosition.add(0);
        this.stackOfCurrentPosition.push(newPosition);

        TermOrFormula returnValue = eqFormula.getLeft().apply(this);

        if( returnValue != null ) {
            return returnValue;
        }

        newPosition = position.shallowcopy();
        newPosition.add(1);
        this.stackOfCurrentPosition.add(newPosition);

        return eqFormula.getRight().apply(this);

    }

    @Override
    public TermOrFormula caseJunctorFormula(JunctorFormula jFormula) {

        Position position = this.stackOfCurrentPosition.pop();

        if( position.equals(this.positionToReturn)) {
            return jFormula.deepcopy();
        }

        Position newPosition = position.shallowcopy();
        newPosition.add(0);
        this.stackOfCurrentPosition.push(newPosition);

        TermOrFormula returnValue = jFormula.getLeft().apply(this);

        if(returnValue != null) {
            return returnValue;
        }

        if( !(jFormula instanceof Not) ) {

            newPosition = position.shallowcopy();
            newPosition.add(1);
            this.stackOfCurrentPosition.push(newPosition);

            return jFormula.getRight().apply(this);

        }

        return null;
    }

}


