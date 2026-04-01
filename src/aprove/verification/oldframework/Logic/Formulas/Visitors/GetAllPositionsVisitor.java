package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;


public class GetAllPositionsVisitor implements CoarseFormulaVisitor, CoarseGrainedTermVisitor {

    protected Stack<Position> stackOfPositions;

    protected Set<Position> positions;

    public static Set<Position> apply(Formula formula) {

        GetAllPositionsVisitor thisVisitor =
            new GetAllPositionsVisitor();

        formula.apply(thisVisitor);

        return thisVisitor.positions;
    }

    public static Set<Position> apply(AlgebraTerm term) {

        GetAllPositionsVisitor thisVisitor =
            new GetAllPositionsVisitor();

        term.apply(thisVisitor);

        return thisVisitor.positions;

    }

    protected GetAllPositionsVisitor() {
        this.positions  = new LinkedHashSet<Position>();
        this.stackOfPositions = new Stack<Position>();
    }

    @Override
    public Object caseTruthValue(FormulaTruthValue truthvalFormula) {

        Position position;

        if( this.stackOfPositions.isEmpty() ) {
            position = Position.create();
        } else {
            position = this.stackOfPositions.pop();
        }

        this.positions.add(position);
        return this.positions;
    }


    @Override
    public Object caseEquation(Equation eqFormula) {

        Position position;

        if(this.stackOfPositions.isEmpty()) {
            position = Position.create();
        } else {
            position = this.stackOfPositions.pop();
        }

        this.positions.add(position);

        Position newPosition = position.shallowcopy();

        newPosition.add(1);
        this.stackOfPositions.push(newPosition);
        eqFormula.getLeft().apply(this);

        newPosition = position.shallowcopy();

        newPosition.add(2);
        this.stackOfPositions.push(newPosition);
        eqFormula.getRight().apply(this);

        return this.positions;
    }

    @Override
    public Object caseJunctorFormula(JunctorFormula jFormula) {

        Position position;

        if( this.stackOfPositions.isEmpty() ) {
            position = Position.create();
        } else {
            position = this.stackOfPositions.pop();
        }

        this.positions.add(position);

        Position newPosition = position.shallowcopy();
        newPosition.add(1);

        this.stackOfPositions.push(newPosition);
        jFormula.getLeft().apply(this);

        if( !(jFormula instanceof Not) ) {

            newPosition = position.shallowcopy();
            newPosition.add(2);

            jFormula.getRight().apply(this);
        }

        return this.positions;
    }


    @Override
    public Object caseVariable(AlgebraVariable v) {

        Position position;

        if( this.stackOfPositions.isEmpty() ){
            position = Position.create();
        } else {
            position = this.stackOfPositions.pop();
        }

        this.positions.add(position);
        return this.positions;
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {

        Position position;

        if( this.stackOfPositions.isEmpty()) {
            position = Position.create();
        }else{
            position = this.stackOfPositions.pop();
        }

        this.positions.add(position);


        List<AlgebraTerm> arguments = f.getArguments();
        for( int i = 0; i < arguments.size(); i++) {

            AlgebraTerm argument = arguments.get(i);

            Position newPosition = position.shallowcopy();
            newPosition.add(i+1);

            this.stackOfPositions.push( newPosition );
            argument.apply(this);
        }

        return this.positions;
    }

}


