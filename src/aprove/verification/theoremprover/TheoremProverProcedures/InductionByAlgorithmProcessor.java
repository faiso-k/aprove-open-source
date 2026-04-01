/*
 * Created on 24.08.2004
 *
 */
package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.input.*;
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
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * @author rabe
 */
public class InductionByAlgorithmProcessor extends TheoremProverProcessor {

    /**
     * Stores algorithm's name, which should be used for
     * axiom generation
     */
    private final String inductionAlgorithm;

    /**
     * Standard constructor
     */
    @ParamsViaArgumentObject
    public InductionByAlgorithmProcessor(Arguments arguments) {
        this.inductionAlgorithm = arguments.inductionAlgorithm;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
                RuntimeInformation rti) throws AbortionException {

        /**
         * Check if processor is applicable
         */
        Formula formula  = obligationInput.getFormula();

        AlgebraTerm inductionAlgorithmAsTerm;

        // check if a algorithm for the given formula is selected
        if( this.inductionAlgorithm == null ) {
            return ResultFactory.notApplicable();
        }

        // assure that selected function symbol is a defined algorithm and not a
        // constructor
        Program program = obligationInput.getProgram();

        try {
            inductionAlgorithmAsTerm = EasyInput.parseTERM(program,this.inductionAlgorithm);
            if(!(inductionAlgorithmAsTerm instanceof DefFunctionApp)) {
                return ResultFactory.notApplicable();
            }
        }
        catch(Exception e) {
            return ResultFactory.notApplicable();
        }

        // initialize used sets
        Set<TheoremProverObligation> baseCases      = new LinkedHashSet<TheoremProverObligation>();
        Set<TheoremProverObligation> stepCases      = new LinkedHashSet<TheoremProverObligation>();

        AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)inductionAlgorithmAsTerm;

        Set<AlgebraVariable> variablesInFormula   = formula.getAllVariables();

        Set<Rule> renamedRulesForAlgorithm = new LinkedHashSet<Rule>();
        for( Rule rule : program.getRules(functionApplication.getFunctionSymbol()) ) {
            renamedRulesForAlgorithm.add(rule.replaceVariables(variablesInFormula));
        }

        Set<HypothesisPair> hypothesesSet;

        for(Rule rule : renamedRulesForAlgorithm) {

            hypothesesSet = new LinkedHashSet<HypothesisPair>();

            AlgebraSubstitution substitution;

            for (AlgebraTerm subTerm : rule.getRight().getAllSubterms()) {
                try {
                    substitution = functionApplication.matches(subTerm);

                    // for some examples evaluation is useful
                    // e.g. for the unsatisfiablity check in conditional evaluation
                    Formula hypothesis = FormulaEvaluationVisitor.apply(formula.apply(substitution),program);

                    Set<VariableSymbol> instanciableVariables = new LinkedHashSet<VariableSymbol>(hypothesis.getAllVariableSymbols());
                    instanciableVariables.removeAll(substitution.getVariableSymbolsInRange());

                    hypothesesSet.add(new HypothesisPair(hypothesis,instanciableVariables));
                }
                catch (UnificationException e) {}
            }

            boolean baseCase;
            if(hypothesesSet.isEmpty()){
                baseCase = true;
            }
            else{
                baseCase = false;
            }

            for(Rule condition : rule.getConds()) {
                hypothesesSet.add(new HypothesisPair(
                        Equation.create(condition.getLeft(), condition.getRight()),
                        new LinkedHashSet<VariableSymbol>()));
            }

            try {
                substitution = functionApplication.matches(rule.getLeft());

                TheoremProverObligation newObligation = new TheoremProverObligation(formula.apply(substitution),
                        program, hypothesesSet, obligationInput);

                if (baseCase){
                    baseCases.add(newObligation);
                }
                else{
                    stepCases.add(newObligation);
                }
            }
            catch (UnificationException e) {}
        }

        Set<TheoremProverObligation> newObligations = new LinkedHashSet<TheoremProverObligation>(baseCases);
        newObligations.addAll(stepCases);

        return ResultFactory.provedAnd(newObligations,
                        obligationInput.getHypotheses().isEmpty() ? YNMImplication.EQUIVALENT : YNMImplication.SOUND,
                        new InductionByAlgorithmProof(baseCases,
                        stepCases, this.inductionAlgorithm));
    }

    public static class Arguments {
        public String inductionAlgorithm = null;
    }

}