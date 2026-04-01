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
public class GetAllSubPartsOfClassWithPosition<T> implements
        CoarseFormulaVisitor<Map<T,List<Position>>>, CoarseGrainedTermVisitor<Map<T,List<Position>>> {

    protected Class<T> clazz;

    protected Stack<Position> stackOfPositions;

    protected Map<T,List<Position>> subParts;

    @SuppressWarnings("unchecked")
    public static <T> Map<T,List<Position>> apply(Formula formula, Class<T> clazz) {

        GetAllSubPartsOfClassWithPosition thisVisitor =
            new GetAllSubPartsOfClassWithPosition<T>(clazz);

        return (Map<T, List<Position>>) formula.apply(thisVisitor);

    }

    @SuppressWarnings("unchecked")
    public static <T> Map<T,List<Position>> apply(AlgebraTerm term, Class<T> clazz) {

        GetAllSubPartsOfClassWithPosition thisVisitor =
            new GetAllSubPartsOfClassWithPosition<T>(clazz);

        return (Map<T, List<Position>>) term.apply(thisVisitor);

    }

    @SuppressWarnings("unchecked")
    protected GetAllSubPartsOfClassWithPosition(Class<T> clazz) {

        this.clazz = clazz;

        this.stackOfPositions = new Stack<Position>();
        this.stackOfPositions.push(Position.create());

        this.subParts = new LinkedHashMap<T,List<Position>>();
    }

    @Override
    @SuppressWarnings("unchecked")
    public Map<T,List<Position>> caseTruthValue(FormulaTruthValue truthvalFormula) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey(truthvalFormula)) {
            this.subParts.get(truthvalFormula).add(position);
        } else {

            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            if(this.clazz.equals(truthvalFormula.getClass())) {
                this.subParts.put((T) truthvalFormula.deepcopy(),newLinkedList);
            }
        }
        return this.subParts;
    }

    @Override
    @SuppressWarnings("unchecked")
    public Map<T,List<Position>> caseEquation(Equation eqFormula) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey( eqFormula )) {
            this.subParts.get(eqFormula).add(position);
        } else {

            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            if(this.clazz.equals(eqFormula.getClass())) {
                this.subParts.put((T)eqFormula.deepcopy(), newLinkedList);
            }
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
    @SuppressWarnings("unchecked")
    public Map<T,List<Position>> caseJunctorFormula(JunctorFormula jFormula) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey( jFormula )) {
            this.subParts.get(jFormula).add(position);
        } else {

            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            if(this.clazz.equals(jFormula.getClass())) {
                this.subParts.put((T)jFormula.deepcopy(), newLinkedList);
            }

        }

        Position newPosition = position.shallowcopy();
        this.stackOfPositions.push(newPosition.add(0));

        this.stackOfPositions.push(newPosition);
        jFormula.getLeft().apply(this);

        if( !(jFormula instanceof Not) ) {

            newPosition = position.shallowcopy();
            this.stackOfPositions.push(newPosition.add(1));

            jFormula.getRight().apply(this);
        }

        return this.subParts;
    }


    @Override
    @SuppressWarnings("unchecked")
    public Map<T,List<Position>> caseVariable(AlgebraVariable v) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey(v)) {
            this.subParts.get(v).add(position);
        }else{
            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            if(this.clazz.equals(v.getClass())) {
                this.subParts.put((T)v.deepcopy(), newLinkedList);
            }

        }

        return this.subParts;
    }

    @Override
    @SuppressWarnings("unchecked")
    public Map<T,List<Position>> caseFunctionApp(AlgebraFunctionApplication f) {

        Position position = this.stackOfPositions.pop();

        if( this.subParts.containsKey(f)) {
            this.subParts.get(f).add(position);
        } else {

            LinkedList<Position> newLinkedList = new LinkedList<Position>();
            newLinkedList.add(position);

            if(this.clazz.equals(f.getClass())) {
                this.subParts.put((T)f.deepcopy(), newLinkedList);
            }

        }


        List<AlgebraTerm> arguments = f.getArguments();
        for( int i = 0; i < arguments.size(); i++) {

            AlgebraTerm argument = arguments.get(i);

            Position newPosition = position.shallowcopy();
            this.stackOfPositions.push(newPosition.add(i));

            this.stackOfPositions.push( newPosition );
            argument.apply(this);
        }

        return this.subParts;
    }

}
