package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class GetAllModifiablePositionsVisitor implements CoarseFormulaVisitor<Set<Position>>, CoarseGrainedTermVisitor<Set<Position>> {

    protected TermOrFormula     termOrFormula;

    protected Program             program;

    protected Stack<Position>    stackOfPositions;

    protected Set<Position>        setOfmodifiablePositions;

    protected Map<SyntacticFunctionSymbol,Set<Integer>> modifiablePositionForFunctions;

    protected TypeContext       typeContext;

    protected TypeAssumption    typeAssumption;


    public static Set<Position> apply(Formula formula, Program program) {
        GetAllModifiablePositionsVisitor getModifiablePositionsVisitor =
            new GetAllModifiablePositionsVisitor(formula,program);
        return formula.apply(getModifiablePositionsVisitor);
    }

    public static Set<Position> apply(AlgebraTerm term, Program program) {
        GetAllModifiablePositionsVisitor getModifiablePositionsVisitor =
            new GetAllModifiablePositionsVisitor(term, program);
        return term.apply(getModifiablePositionsVisitor);
    }

    protected GetAllModifiablePositionsVisitor(TermOrFormula termOrFormula, Program program) {

        // init object's variables
        this.program = program;
        this.termOrFormula = termOrFormula;
        this.stackOfPositions = new Stack<Position>();
        this.stackOfPositions.push(Position.create());

        this.setOfmodifiablePositions = new LinkedHashSet<Position>();
        this.setOfmodifiablePositions.add(Position.create());

        this.modifiablePositionForFunctions    = new LinkedHashMap<SyntacticFunctionSymbol,Set<Integer>>();

    }

    @Override
    public Set<Position> caseEquation(Equation equation) {

        Position oldPosition = this.stackOfPositions.pop();

        Position tempPosition = oldPosition.shallowcopy();
        tempPosition.add(0);
        this.stackOfPositions.push(tempPosition);

        if (this.setOfmodifiablePositions.contains(oldPosition)) {
            this.setOfmodifiablePositions.add(tempPosition);
        }

        equation.getLeft().apply(this);

        tempPosition = oldPosition.shallowcopy();
        tempPosition.add(1);
        this.stackOfPositions.push(tempPosition);

        if (this.setOfmodifiablePositions.contains(oldPosition)) {
            this.setOfmodifiablePositions.add(tempPosition);
        }

        equation.getRight().apply(this);


        return this.setOfmodifiablePositions;
    }

    @Override
    public Set<Position> caseJunctorFormula(JunctorFormula junctorFormula) {

        Position oldPosition = this.stackOfPositions.pop();

        Position tempPosition = oldPosition.shallowcopy();
        tempPosition.add(0);
        this.stackOfPositions.push(tempPosition);

        if (this.setOfmodifiablePositions.contains(oldPosition)) {
            this.setOfmodifiablePositions.add(tempPosition);
        }

        junctorFormula.getLeft().apply(this);

        tempPosition = oldPosition.shallowcopy();
        tempPosition.add(1);
        this.stackOfPositions.push(tempPosition);

        if (this.setOfmodifiablePositions.contains(oldPosition)) {
            this.setOfmodifiablePositions.add(tempPosition);
        }

        if(junctorFormula.getRight() != null) {
            junctorFormula.getRight().apply(this);
        }

        return this.setOfmodifiablePositions;

    }

    @Override
    public Set<Position> caseTruthValue(FormulaTruthValue truthvalFormula) {
        this.stackOfPositions.pop();
        return this.setOfmodifiablePositions;
    }

    @Override
    public Set<Position> caseFunctionApp(AlgebraFunctionApplication functionApplication) {

        Position oldPosition = this.stackOfPositions.pop();

        SyntacticFunctionSymbol functionSymbol = functionApplication.getFunctionSymbol();

        if( functionSymbol instanceof ConstructorSymbol ) {

            int index = 0;

            for(AlgebraTerm term : functionApplication.getArguments() ) {

                Position tempPosition = oldPosition.shallowcopy();
                tempPosition.add(index);
                // Some little sanity checks.
                if (Globals.useAssertions) {

                    if(term == null){
                        System.out.println(functionApplication);
                    }
                    assert(term != null);

                    if(term.getSort() == null){
                        System.out.println(term);
                    }
                    assert(term.getSort() != null);

                }
                if(!term.getSort().equals(functionSymbol.getSort()) && this.setOfmodifiablePositions.contains(oldPosition)) {
                    this.setOfmodifiablePositions.add(tempPosition);
                }

                this.stackOfPositions.push(tempPosition);
                term.apply(this);

                index++;
            }

        } else {

            int index = 0;

            for(AlgebraTerm term : functionApplication.getArguments()) {

                Position tempPosition = oldPosition.shallowcopy();
                tempPosition.add(index);

                if( !this.modifiablePositionForFunctions.containsKey(functionSymbol)) {
                    this.modifiablePositionForFunctions.put(functionSymbol, functionSymbol.getModifiablePositions(this.program));
                }

                if( this.modifiablePositionForFunctions.get(functionSymbol).contains(index) &&
                    this.setOfmodifiablePositions.contains(oldPosition)) {
                    this.setOfmodifiablePositions.add(tempPosition);
                }

                this.stackOfPositions.push(tempPosition);
                term.apply(this);

                index++;
            }
        }

        return this.setOfmodifiablePositions;
    }

    @Override
    public Set<Position> caseVariable(AlgebraVariable variable) {
        this.stackOfPositions.pop();
        return this.setOfmodifiablePositions;
    }

}
