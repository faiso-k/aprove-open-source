/*
 * Created on 18.08.2004
 *
 */
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
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * @author rabe
 */
public class InductionByDataStructureProcessor extends TheoremProverProcessor {

    private final String inductionVariable;

    @ParamsViaArguments("InductionVariable")
    public InductionByDataStructureProcessor(String inductionVariable) {
        this.inductionVariable = inductionVariable;
    }

    @Override
    protected Result process(TheoremProverObligation input, BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        // check if formula contained in FormulaProgramPair
        Formula formula = input.getFormula();

        // check if a variable is selected for current formula
        if( this.inductionVariable.equals("") ) {
            return ResultFactory.notApplicable();
        }

        VariableSymbol inductionVariable = null;

        for(AlgebraVariable variable : input.getFormula().getAllVariables()) {
            if(variable.getName().equals(this.inductionVariable)) {
                inductionVariable = variable.getVariableSymbol();
            }
        }

        if(inductionVariable == null) {
            return ResultFactory.notApplicable();
        }


        // determine variable's sort and the constructors used by this sort
        Set<ConstructorSymbol> constructorSymbols = input.getProgram().getConstructorSymbols();

        Set<TheoremProverObligation> baseCases = new LinkedHashSet<TheoremProverObligation>();
        Set<TheoremProverObligation> stepCases = new LinkedHashSet<TheoremProverObligation>();
        Set<TheoremProverObligation> combinedObligations   = new LinkedHashSet<TheoremProverObligation>();
        Set<HypothesisPair> hypotheses  = new LinkedHashSet<HypothesisPair>();

        // search for ground constructor symbols
        for(ConstructorSymbol  constructorSymbol: constructorSymbols) {

            // check if constructor is of same type as the induction variable,
            // both types do not match process next constructor
            if( !constructorSymbol.getSort().equals(inductionVariable.getSort())) {
                continue;
            }

            // create base cases by instantiating induction variable
            // with ground constructor symbols
            if( constructorSymbol.isConstant() ) {

                // create the substitution
                AlgebraSubstitution substitution = AlgebraSubstitution.create();
                substitution.put(inductionVariable, AlgebraFunctionApplication.create(constructorSymbol));

                // apply substitution
                Formula instance = formula.apply( substitution );

                TheoremProverObligation newObligation = new TheoremProverObligation(instance,input.getProgram());

                // add instance to the base cases
                baseCases.add( newObligation );

                combinedObligations.add(newObligation);


            } else {

                // initial hypotheses set
                hypotheses = new LinkedHashSet<HypothesisPair>();

                // create arguments for constructor
                List<AlgebraVariable> arguments = new LinkedList<AlgebraVariable>();

                FreshVarGenerator freshVarGenerator = new FreshVarGenerator(formula.getAllVariables());

                for(int i=0; i< constructorSymbol.getArity(); i++) {
                    AlgebraVariable freshVariable = freshVarGenerator.getFreshVariable("n",constructorSymbol.getArgSort(i),false);

                    if(constructorSymbol.isReflexivePosition(i)) {

                        AlgebraSubstitution sub = AlgebraSubstitution.create();
                        sub.put(inductionVariable, freshVariable);

                        Formula hypothesis = formula.apply(sub);

                        Set<VariableSymbol> instanciableVariables = hypothesis.getAllVariableSymbols();
                        instanciableVariables.remove(freshVariable.getSymbol());

                        hypotheses.add(new HypothesisPair(FormulaEvaluationVisitor.apply(hypothesis, input.getProgram()),
                            instanciableVariables));

                    }
                    arguments.add(freshVariable);
                }


                // create substitution
                AlgebraSubstitution substitution = AlgebraSubstitution.create();
                substitution.put( inductionVariable, AlgebraFunctionApplication.create(constructorSymbol, arguments));

                // apply substitution
                Formula instance = formula.apply(substitution);

                TheoremProverObligation newObligation  =  new TheoremProverObligation(instance, input.getProgram(),
                        hypotheses, input);

                // add instance to the step cases
                stepCases.add( newObligation );

                combinedObligations.add( newObligation );
            }

        }

        return ResultFactory.provedAnd(combinedObligations,
                input.getHypotheses().isEmpty() ? YNMImplication.EQUIVALENT : YNMImplication.SOUND,
                new InductionByDataStructureProof(baseCases, stepCases, inductionVariable.getSort().getName()));
    }

}
