package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

public class GenerateAnnotatedFormulaVisitor implements FineFormulaVisitor<Formula>,FineGrainedTermVisitor<AlgebraTerm> {

    protected final String          waveHoleSymbol;
    protected final String          waveFrontInSymbol;
    protected final String          waveFrontOutSymbol;

    protected Program            program;
    protected Set<Position>      waveHoles;
    protected Set<Position>      waveFrontsInwards;
    protected Set<Position>         waveFrontOutwards;
    protected Stack<Position>    stackOfPositions;
    protected Stack<AlgebraTerm>         stackOfTerms;

    public static AlgebraTerm apply(AlgebraTerm term, Program program, Set<Position> waveHolesInwards, Set<Position> waveHolesOutwards) {
        return (AlgebraTerm)term.apply(new GenerateAnnotatedFormulaVisitor(program, waveHolesInwards, waveHolesOutwards));
    }

    public static Formula apply(Formula formula, Program program, Set<Position> waveHolesInwards, Set<Position> waveHolesOutwards) {
        return (Formula)formula.apply(new GenerateAnnotatedFormulaVisitor(program, waveHolesInwards, waveHolesOutwards));
    }

    public GenerateAnnotatedFormulaVisitor(Program program, Set<Position> waveHolesInwards, Set<Position> waveHolesOutwards) {

        this.program = program;

        this.waveHoles = new LinkedHashSet<Position>(waveHolesInwards);
        this.waveHoles.addAll(waveHolesOutwards);

        this.waveFrontsInwards = new LinkedHashSet<Position>();
        for(Position position: waveHolesInwards){
            this.waveFrontsInwards.add(position.pred());
        }

        this.waveFrontOutwards = new LinkedHashSet<Position>();
        for(Position position: waveHolesOutwards){
            this.waveFrontOutwards.add(position.pred());
        }

        this.stackOfPositions   = new Stack<Position>();
        this.stackOfPositions.push(Position.create());

        this.stackOfTerms = new Stack<AlgebraTerm>();

        this.waveHoleSymbol       = this.program.getWaveHoleSymbol().getName();
        this.waveFrontInSymbol    = this.program.getWaveFrontInSymbol().getName();
        this.waveFrontOutSymbol   = this.program.getWaveFrontOutSymbol().getName();
    }



    @Override
    public Formula caseAnd(And andFormula) {
        Position position = this.stackOfPositions.pop();

        this.stackOfPositions.push(position.shallowcopy().add(0));
        Formula leftFormula = andFormula.getLeft().apply(this);

        this.stackOfPositions.push(position.shallowcopy().add(1));
        Formula rightFormula = andFormula.getRight().apply(this);

        return And.create(leftFormula, rightFormula);
    }

    @Override
    public Formula caseEquation(Equation phi) {
        Position position = this.stackOfPositions.pop();

        this.stackOfPositions.push(position.shallowcopy().add(0));
        AlgebraTerm leftTerm  = phi.getLeft().apply(this);

        this.stackOfPositions.push(position.shallowcopy().add(1));
        AlgebraTerm rightTerm = phi.getRight().apply(this);

        return Equation.create(leftTerm, rightTerm);
    }

    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {
        Position position = this.stackOfPositions.pop();

        this.stackOfPositions.push(position.shallowcopy().add(0));
        Formula leftFormula = equivFormula.getLeft().apply(this);

        this.stackOfPositions.push(position.shallowcopy().add(1));
        Formula rightFormula = equivFormula.getRight().apply(this);

        return Equivalence.create((Formula)leftFormula, (Formula)rightFormula);
    }

    @Override
    public Formula caseImplication(Implication implFormula) {
        Position position = this.stackOfPositions.pop();

        this.stackOfPositions.push(position.shallowcopy().add(0));
        Formula leftFormula = implFormula.getLeft().apply(this);

        this.stackOfPositions.push(position.shallowcopy().add(1));
        Formula rightFormula = implFormula.getRight().apply(this);

        return Implication.create(leftFormula, rightFormula);
    }

    @Override
    public Formula caseNot(Not notFormula) {
        this.stackOfPositions.push(this.stackOfPositions.pop().shallowcopy().add(0));
        return Not.create(notFormula.getLeft().apply(this));
    }

    @Override
    public Formula caseOr(Or orFormula) {
        Position position = this.stackOfPositions.pop();

        this.stackOfPositions.push(position.shallowcopy().add(0));
        Formula leftFormula = orFormula.getLeft().apply(this);

        this.stackOfPositions.push(position.shallowcopy().add(1));
        Formula rightFormula = orFormula.getRight().apply(this);

        return Or.create(leftFormula,rightFormula);
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        this.stackOfPositions.pop();
        return truthvalFormula.deepcopy();
    }

    @Override
    public AlgebraTerm caseConstructorApp(ConstructorApp cterm) {

        Position currentPosition = this.stackOfPositions.pop();

        for(int index=0; index < cterm.getFunctionSymbol().getArity(); index++) {

            Position newPosition = currentPosition.shallowcopy();
            newPosition.add(index);

            this.stackOfPositions.push(newPosition);
            cterm.getArgument(index).apply(this);

        }

        if(cterm.isConstant()) {

            if(this.waveHoles.contains(currentPosition)){
                this.stackOfTerms.push(MetaFunctionApplication.create(WaveHole.create(this.waveHoleSymbol,1),cterm.deepcopy()));
            }else{
                this.stackOfTerms.push(cterm.deepcopy());
            }

        }else{

            AlgebraTerm annotatedTerm;
            LinkedList<AlgebraTerm> args = new LinkedList<AlgebraTerm>();

            for(int index=0; index < cterm.getFunctionSymbol().getArity(); index++) {
                args.addFirst(this.stackOfTerms.pop());
            }

            annotatedTerm = AlgebraFunctionApplication.create(cterm.getFunctionSymbol(),args);

            if(this.waveFrontsInwards.contains(currentPosition)) {
                annotatedTerm = MetaFunctionApplication.create(WaveFrontIn.create(this.waveFrontInSymbol,1),annotatedTerm);
            } else if(this.waveFrontOutwards.contains(currentPosition)) {
                annotatedTerm = MetaFunctionApplication.create(WaveFrontOut.create(this.waveFrontOutSymbol,1),annotatedTerm);
            }

            if( this.waveHoles.contains(currentPosition)) {
                 annotatedTerm = MetaFunctionApplication.create(WaveHole.create(this.waveHoleSymbol,1), annotatedTerm);
            }

            this.stackOfTerms.push(annotatedTerm);
        }

        return this.stackOfTerms.peek();
    }

    @Override
    public AlgebraTerm caseDefFunctionApp(DefFunctionApp fterm) {

        Position currentPosition = this.stackOfPositions.pop();

        for(int index=0; index < fterm.getFunctionSymbol().getArity(); index++) {

            Position newPosition = currentPosition.shallowcopy();
            newPosition.add(index);

            this.stackOfPositions.push(newPosition);
            fterm.getArgument(index).apply(this);

        }

        LinkedList<AlgebraTerm> args = new LinkedList<AlgebraTerm>();

        for(int index=0; index < fterm.getFunctionSymbol().getArity(); index++) {
            args.addFirst(this.stackOfTerms.pop());
        }

        AlgebraTerm annotatedTerm = AlgebraFunctionApplication.create(fterm.getFunctionSymbol(),args);

        if(this.waveFrontsInwards.contains(currentPosition)) {
             annotatedTerm = MetaFunctionApplication.create(WaveFrontIn.create(this.waveFrontInSymbol,1), annotatedTerm);
        } else if(this.waveFrontOutwards.contains(currentPosition)) {
             annotatedTerm = MetaFunctionApplication.create(WaveFrontOut.create(this.waveFrontOutSymbol,1),annotatedTerm);
        }

        if( this.waveHoles.contains(currentPosition)) {
            annotatedTerm = MetaFunctionApplication.create(WaveHole.create(this.waveHoleSymbol,1), annotatedTerm);
        }


        this.stackOfTerms.push(annotatedTerm);

        return this.stackOfTerms.peek();

    }

    @Override
    public AlgebraTerm caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        throw new RuntimeException("Should not be applied to formulas, which are already annotated");
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {

        Position currentPosition = this.stackOfPositions.pop();

        if(this.waveHoles.contains(currentPosition)) {
            this.stackOfTerms.push(MetaFunctionApplication.create(WaveHole.create(this.waveHoleSymbol,1),v.deepcopy()));
        }else{
            this.stackOfTerms.push(v.deepcopy());
        }

        return this.stackOfTerms.peek();
    }

}
