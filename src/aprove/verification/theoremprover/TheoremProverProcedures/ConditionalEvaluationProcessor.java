package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

@NoParams
public class ConditionalEvaluationProcessor extends TheoremProverProcessor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        // deactivate for strs
        // actually deactivating only for semi la based function symbols might have been ok, too
        // but now we have a conditional rewriting processor
        if (obl instanceof TheoremProverObligation) {
            TheoremProverObligation theorem_obl = (TheoremProverObligation) obl;

            if (theorem_obl.getProgram().laProgramProperties != null){
                return false;
            }
            else{
                return true;
            }
        }
        return false;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        Formula formula = obligationInput.getFormula();

        ConditionalEvaluationVisitor conditionalEvaluationVisitor = new ConditionalEvaluationVisitor(
                obligationInput.getProgram());
        formula.apply(conditionalEvaluationVisitor);

        try {

            if(conditionalEvaluationVisitor.positionToRewrite != null) {

                Set<TheoremProverObligation> newObligations = new LinkedHashSet<TheoremProverObligation>();

                AlgebraTerm termToRewrite = (AlgebraTerm)formula.getSubPart(conditionalEvaluationVisitor.positionToRewrite);

                for(Rule rule : conditionalEvaluationVisitor.rulesToUse) {

                    List<Formula> premises = new Vector<Formula>();

                    AlgebraSubstitution substitution = rule.getLeft().matches(termToRewrite);

                    for(Rule cond: rule.getConds()) {
                        Formula newFormula = Equation.create(cond.getLeft().apply(substitution),
                                cond.getRight().apply(substitution));
                        premises.add(newFormula);
                    }

                    Formula rightHandOfImplication = formula.replaceTermAt(rule.getRight().apply(substitution),
                            conditionalEvaluationVisitor.positionToRewrite);

                    if(this.isConsitent(premises, obligationInput.getHypothesesAsSet(), obligationInput.getProgram())) {
                        TheoremProverObligation newObligation = new TheoremProverObligation(rightHandOfImplication,obligationInput);
                        for(Formula premise : premises) {
                            newObligation.addHypothesis(premise, new LinkedHashSet<VariableSymbol>());
                        }

                        newObligations.add(newObligation);
                    }
                }

                return ResultFactory.provedAnd(newObligations,YNMImplication.EQUIVALENT, new ConditionalEvaluationProof(newObligations));

            }
        }
        catch(Exception e) {}

        return ResultFactory.notApplicable();
    }

    protected boolean isConsitent(List<Formula> premises, Set<HypothesisPair> hypotheses,Program program) {

        boolean consistent = true;

        // Get all hypotheses, which are realy allquantified
        Set<Formula> hypothesesSet = new LinkedHashSet<Formula>(premises);
        for(Pair<Formula,Set<VariableSymbol>> hypothesis : hypotheses) {
            if(hypothesis.y.isEmpty()) {
                hypothesesSet.add(hypothesis.x);
            }
        }

        // simply check for a inconsistent hypothesis set
        for(Formula hypothesis : hypothesesSet) {

            if(FormulaEvaluationVisitor.apply(hypothesis, program).equals(FormulaTruthValue.FALSE)) {
                consistent = false;
                break;
            }

            if(hypothesesSet.contains(Not.create(hypothesis))) {
                consistent =false;
                break;
            }

            if(hypothesis.isEquation()) {

                Equation equation = (Equation)hypothesis;

                if(equation.getRight().getSymbol().equals(program.getSymbol("false"))) {

                    Symbol leftSymbol = equation.getLeft().getSymbol();

                    if(program.getPredefFunctionSymbols().contains(leftSymbol) && leftSymbol.getName().startsWith("equal_") ) {

                        if(equation.getLeft().getArgument(0).equals(equation.getLeft().getArgument(1))) {
                            consistent = false;
                            break;
                        }
                    }
                }

                if(equation.getLeft().getSymbol().equals(program.getSymbol("false"))) {

                    Symbol rightSymbol = equation.getRight().getSymbol();

                    if(program.getPredefFunctionSymbols().contains(rightSymbol) && rightSymbol.getName().startsWith("equal_") ) {

                        if(equation.getRight().getArgument(0).equals(equation.getRight().getArgument(1))) {
                            consistent = false;
                            break;
                        }
                    }
                }

                if(equation.getLeft().getSymbol().equals(program.getSymbol("true"))){

                    Equation inverseEquation = Equation.create(ConstructorApp.create(program.getConstructorSymbol("false")),
                            equation.getRight());

                    if(hypothesesSet.contains(inverseEquation)) {
                        consistent = false;
                        break;
                    }
                }

                if(equation.getRight().getSymbol().equals(program.getSymbol("true"))){

                    Equation inverseEquation = Equation.create(equation.getLeft(),
                            ConstructorApp.create(program.getConstructorSymbol("false")));

                    if(hypothesesSet.contains(inverseEquation)) {
                        consistent = false;
                        break;
                    }

                }
            }

        }

        return consistent;

    }
}

// finds the first positionn where the conditional rewriting is possible
// and marks the applicable rules at this position
class ConditionalEvaluationVisitor implements CoarseFormulaVisitor<Object>, CoarseGrainedTermVisitor<Object> {

    protected Map<String,Set<Rule>> rules;

    private Stack<Position>  stackOfPositions;
    boolean                     alreadyFound;
    Position                 positionToRewrite;
    Set<Rule>                  rulesToUse;
    Position                  equationPosition;

    protected ConditionalEvaluationVisitor(Program program) {

        this.alreadyFound = false;

        this.rules   = program.getRuleMapping();

        this.stackOfPositions   = new Stack<Position>();
        this.stackOfPositions.push(Position.create());

        this.rulesToUse            = new LinkedHashSet<Rule>();

    }

    @Override
    public Object caseTruthValue(FormulaTruthValue truthvalFormula) {
        this.stackOfPositions.pop();
        return null;
    }

    @Override
    public Object caseEquation(Equation eqFormula) {

        Position position = this.stackOfPositions.pop();

        this.equationPosition = position;

        this.stackOfPositions.push(position.shallowcopy().add(0));
        eqFormula.getLeft().apply(this);

        this.stackOfPositions.push(position.shallowcopy().add(1));
        eqFormula.getRight().apply(this);

        return null;
    }

    @Override
    public Object caseJunctorFormula(JunctorFormula jFormula) {

        Position position = this.stackOfPositions.pop();

        this.stackOfPositions.push(position.shallowcopy().add(0));
        jFormula.getLeft().apply(this);

        if(!(jFormula instanceof Not)) {
            this.stackOfPositions.push(position.shallowcopy().add(1));
            jFormula.getRight().apply(this);
        }

        return null;
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        this.stackOfPositions.pop();
        return null;
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {

        Position position = this.stackOfPositions.pop();

        for(int i=0; i < f.getArguments().size(); i++) {
            this.stackOfPositions.push( position.shallowcopy().add(i));
            f.getArgument(i).apply(this);
        }

        Set<Rule> funcRules = this.rules.get(f.getFunctionSymbol().getName());

        if((funcRules != null) && !this.alreadyFound) {

            for(Rule rule : funcRules) {

                if(rule.getConds().size() == 0) {
                    continue;
                }

                try {
                    Rule renamedRule = rule.replaceVariables(f.getVars());
                    renamedRule.getLeft().matches(f);
                    this.positionToRewrite = position;
                    this.alreadyFound = true;
                    this.rulesToUse.add(rule);
                }catch(UnificationException e) {}

            }

            if(this.rulesToUse.size() > 0) {
                return null;
            }

        }

        return null;
    }

}
