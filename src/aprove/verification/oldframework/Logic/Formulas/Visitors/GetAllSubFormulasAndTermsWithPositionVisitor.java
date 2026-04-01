/*
 * Created on 28.10.2004
 */
package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * @author rabe
 */
public class GetAllSubFormulasAndTermsWithPositionVisitor implements
        CoarseFormulaVisitor<Map<TermOrFormula,List<Position>>>, CoarseGrainedTermVisitor<Map<TermOrFormula,List<Position>>> {

    protected Stack<Position> stackOfPositions;

    protected Map<TermOrFormula,List<Position>> subParts;

    public static Map<TermOrFormula,List<Position>> apply(Formula formula) {

        GetAllSubFormulasAndTermsWithPositionVisitor thisVisitor =
            new GetAllSubFormulasAndTermsWithPositionVisitor();

        return formula.apply(thisVisitor);

    }

    public static Map<TermOrFormula,List<Position>> apply(AlgebraTerm term) {

        GetAllSubFormulasAndTermsWithPositionVisitor thisVisitor =
            new GetAllSubFormulasAndTermsWithPositionVisitor();

        return term.apply(thisVisitor);

    }

    protected GetAllSubFormulasAndTermsWithPositionVisitor() {

        this.stackOfPositions = new Stack<Position>();
        this.stackOfPositions.push(Position.create());

        this.subParts = new LinkedHashMap<TermOrFormula,List<Position>>();
    }

    @Override
    public Map<TermOrFormula,List<Position>> caseTruthValue(FormulaTruthValue truthvalFormula) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey(truthvalFormula)) {
            this.subParts.get(truthvalFormula).add(position);
        } else {

            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            this.subParts.put(truthvalFormula.deepcopy(),newLinkedList);
        }
        return this.subParts;
    }


    @Override
    public Map<TermOrFormula,List<Position>> caseEquation(Equation eqFormula) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey( eqFormula )) {
            this.subParts.get(eqFormula).add(position);
        } else {

            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            this.subParts.put(eqFormula.deepcopy(), newLinkedList);
        }

        Position newPosition = position.shallowcopy();

        newPosition.add(0);
        this.stackOfPositions.push(newPosition);
        eqFormula.getLeft().apply(this);

        newPosition = position.shallowcopy();

        newPosition.add(1);
        this.stackOfPositions.push(newPosition);
        eqFormula.getRight().apply(this);

        return this.subParts;
    }




    @Override
    public Map<TermOrFormula,List<Position>> caseJunctorFormula(JunctorFormula jFormula) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey( jFormula )) {
            this.subParts.get(jFormula).add(position);
        } else {

            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            this.subParts.put(jFormula.deepcopy(), newLinkedList);

        }

        Position newPosition = position.shallowcopy();
        newPosition.add(0);

        this.stackOfPositions.push(newPosition);
        jFormula.getLeft().apply(this);

        if( !(jFormula instanceof Not) ) {

            newPosition = position.shallowcopy();
            newPosition.add(1);
            this.stackOfPositions.push(newPosition);

            jFormula.getRight().apply(this);
        }

        return this.subParts;
    }


    @Override
    public Map<TermOrFormula,List<Position>> caseVariable(AlgebraVariable v) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey(v)) {
            this.subParts.get(v).add(position);
        }else{
            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            this.subParts.put(v.deepcopy(), newLinkedList);

        }

        return this.subParts;
    }

    @Override
    public Map<TermOrFormula,List<Position>> caseFunctionApp(AlgebraFunctionApplication f) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey(f)) {
            this.subParts.get(f).add(position);
        } else {

            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            this.subParts.put(f.deepcopy(), newLinkedList);
        }


        List<AlgebraTerm> arguments = f.getArguments();
        for( int i = 0; i < arguments.size(); i++) {

            AlgebraTerm argument = arguments.get(i);

            Position newPosition = position.shallowcopy();
            newPosition.add(i);

            this.stackOfPositions.push( newPosition );
            argument.apply(this);
        }

        return this.subParts;
    }

}
