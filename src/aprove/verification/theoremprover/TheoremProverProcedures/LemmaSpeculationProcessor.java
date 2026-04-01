package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.DifferenceUnification.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

@NoParams
public class LemmaSpeculationProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        // get formula and hypotheses
        Formula formula = obligationInput.getFormula();
        Set<HypothesisPair> hypotheses = obligationInput.getHypothesesAsSet();

        // get all formulas contained in formula
        List<Equation> formulaEquations    = formula.getAllEquations();

        // get all equations contained in hypotheses
        List<Equation> hypothesesEquations = new Vector<Equation>();
        for(Pair<Formula,Set<VariableSymbol>> hypothesis : hypotheses) {
            hypothesesEquations.addAll(hypothesis.x.getAllEquations());
        }

        TreeMap<Integer,Triple<Equation, Equation, Set<Position>>> sortedResults =
            new TreeMap<Integer,Triple<Equation,Equation,Set<Position>>>();

        for(Equation formulaEquation : formulaEquations) {
            for(Equation hypothesisEquation : hypothesesEquations) {

                Set<Triple<Set<Position>,Set<Position>,AlgebraSubstitution>> results =
                    DifferenceUnification.apply(formulaEquation.getLeft(), hypothesisEquation.getLeft());

                // get only those result wich consists of variable renaming and the skeleton
                // is not a variable. Order them ascending according to the number of annotations
                for(Triple<Set<Position>,Set<Position>,AlgebraSubstitution> result : results) {

                    if(result.z.isVariableRenaming() && !( GetSkeletonVisitor.apply(formulaEquation.getLeft(), result.x).isVariable()
                      || GetSkeletonVisitor.apply(hypothesisEquation.getLeft(), result.y).isVariable())) {

                        sortedResults.put(result.x.size()+result.y.size(),new Triple<Equation,Equation,Set<Position>>(
                                formulaEquation,hypothesisEquation,result.x));
                    }
                }

            }
        }

        try {

            for(Triple<Equation,Equation,Set<Position>> result : sortedResults.values()) {

                for(Position position : result.z) {

                    AlgebraTerm leftPartOfFormula = result.getX().getLeft();

                    Position positionOfConflict = position.pred();

                    // get conflicting term and its result type
                    AlgebraTerm conflictTerm = leftPartOfFormula.getSubterm(positionOfConflict);

                    if(!(conflictTerm instanceof ConstructorApp)) {
                        continue;
                    }

                    Sort sortOfConflictTerm = conflictTerm.getSymbol().getSort();

                    for(int i=0; i < positionOfConflict.size(); i++) {

                        Position actualPosition = positionOfConflict.pred();

                        AlgebraTerm candidateTerm = leftPartOfFormula.getSubterm(actualPosition);

                        if( !candidateTerm.isVariable() ) {

                            AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)candidateTerm;

                            for(Integer argumentIndex : functionApplication.getFunctionSymbol().
                                    getModifiablePositions(obligationInput.getProgram())) {

                                Sort argumentSort = functionApplication.getSymbol().getSort();

                                if(argumentSort.equals(sortOfConflictTerm)) {

                                    AlgebraTerm newRightHandSide = leftPartOfFormula.deepcopy();

                                    Position positionToReplace = actualPosition.shallowcopy();
                                    positionToReplace.add(argumentIndex);

                                    newRightHandSide = newRightHandSide.replaceAt(conflictTerm,positionToReplace);
                                    newRightHandSide = newRightHandSide.replaceAt(leftPartOfFormula.getSubterm(positionToReplace),
                                            positionOfConflict);

                                    Equation lemma = this.substituteCommonSubterms(Equation.create(leftPartOfFormula.deepcopy().
                                            getSubterm(actualPosition), newRightHandSide.getSubterm(actualPosition)));

                                    Set<Formula> lemmas = new LinkedHashSet<Formula>();
                                    lemmas.add(lemma);

                                    Set<TheoremProverObligation> newObligations = new LinkedHashSet<TheoremProverObligation>();

                                    TheoremProverObligation newTheoremProverObligation = new TheoremProverObligation
                                    (LemmaApplicationVisitorOld.apply(obligationInput.getFormula(), lemmas).getKey(), obligationInput);

                                    newObligations.add(newTheoremProverObligation);
                                    newObligations.add(new TheoremProverObligation(lemma, obligationInput.getProgram()));

                                    return ResultFactory.provedAnd(newObligations, YNMImplication.SOUND,
                                            new LemmaSpeculationProof(lemma, newObligations));
                                }

                            }

                        }

                    }

                }

            }

        }catch(Exception e) {
            e.printStackTrace();
        }

        return ResultFactory.notApplicable();
    }

    protected Equation substituteCommonSubterms(Equation equation) {

        FreshVarGenerator freshVarGenerator = new FreshVarGenerator(equation.getAllVariables());

        Equation generalisedEquation = (Equation)equation.deepcopy();

        for(Map.Entry<TermOrFormula,List<Position>> entry : equation.getAllSubFormulasAndTermsWithPosition().entrySet()) {

            if (entry.getKey().isTerm() && (entry.getKey() instanceof ConstructorApp) && !((AlgebraTerm) entry.getKey()).isVariable() &&
                entry.getValue().size() > 1) {

                AlgebraVariable variable = freshVarGenerator.getFreshVariable("z",((AlgebraTerm)entry.getKey()).getSort(),false);

                for (Position position : entry.getValue()) {
                    try {
                        generalisedEquation = (Equation) generalisedEquation.replaceTermAt(variable, position);
                    } catch (InvalidPositionException e) {
                        throw new RuntimeException(e.getMessage());
                    }
                }


            }

        }

        return generalisedEquation;
    }


}
