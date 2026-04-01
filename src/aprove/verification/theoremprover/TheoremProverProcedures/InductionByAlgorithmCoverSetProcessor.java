package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Implication;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProcedures.Induction.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * @author dickmeis
 */
public class InductionByAlgorithmCoverSetProcessor extends
        TheoremProverProcessor {

    // the position where the induction should be done
    private final List<Position> positions;

    private final boolean skipLAHypothesisHeuristic;

    private final boolean evaluateHypothesis;

    /**
     * Standard constructor
     */
    @ParamsViaArgumentObject
    public InductionByAlgorithmCoverSetProcessor(Arguments arguments) {
        this.positions = this.parsePositions(arguments.positions);
        this.evaluateHypothesis = arguments.evaluateHypothesis;
        this.skipLAHypothesisHeuristic = arguments.skipLAHypothesisHeuristic;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        /**
         * Check if processor is applicable
         */
        Formula formula = obligationInput.getFormula();

        Program program = obligationInput.getProgram();

        LAProgramProperties laProgram = program.laProgramProperties;

        List<Position> localPositions = new ArrayList<Position>(this.positions.size());
        for (Position position : this.positions) {
            localPositions.add(position.deepcopy());
        }

        if(localPositions.isEmpty()){
            return ResultFactory.notApplicable("No position defined.");
        }

        boolean laInduction = true;
        boolean constructorInduction = true;
        boolean variableInduction = true;

        List<Pair<AlgebraTerm, Position>> termsWithPosition = new ArrayList<Pair<AlgebraTerm,Position>>(localPositions.size());

        for (Position localPosition : localPositions) {

            AlgebraTerm inductionTerm;

            try {
                inductionTerm = (AlgebraTerm) formula.getSubPart(localPosition);

                // assure that selected function symbol is a defined algorithm and not a
                // constructor
                if (inductionTerm instanceof DefFunctionApp) {
                    DefFunctionApp defapp = (DefFunctionApp) inductionTerm;
                    SyntacticFunctionSymbol functionSymbol = defapp.getFunctionSymbol();
                    List<AlgebraTerm> args = defapp.getArguments();

                    ArrayList<AlgebraVariable> disjunctVars = new ArrayList<AlgebraVariable>(args.size());

                    boolean disjunct = true;
                    boolean laBased = laProgram != null;

                    CoverSet cs = CoverSet.createCoverSet(functionSymbol, new HashSet<AlgebraVariable>(), program);

                    boolean constructorBased = cs.isConstructorBased();

                    if(laBased){
                        SyntacticFunctionSymbol fsym = defapp.getFunctionSymbol();
                        if(! laProgram.laBasedFunctionSymbols.contains(fsym)){
                            laBased = false;
                        }
                    }

                    for (AlgebraTerm term : args) {
                        if (disjunct){
                            if(term instanceof AlgebraVariable) {
                                AlgebraVariable var = (AlgebraVariable) term;

                                if(disjunctVars.contains(var)){
                                    // not disjunct
                                    disjunct = false;
                                }
                            }
                            else{
                                disjunct = false;
                            }
                        }

                        if(laBased){
                            laBased = laBased && term.isLA(laProgram);
                        }

                        if(constructorBased){
                            constructorBased = constructorBased && term.isConstructorTerm();
                        }
                    }

                    laInduction = laInduction && laBased;
                    constructorInduction = constructorInduction && constructorBased;
                    variableInduction = variableInduction && disjunct;

                    Pair<AlgebraTerm, Position> p = new Pair<AlgebraTerm, Position>(inductionTerm,localPosition);
                    termsWithPosition.add(p);
                }
                else{
                    return ResultFactory.notApplicable("Not a position of a defined function application: " + localPosition);
                }

            }
            catch (Exception e) {
                return ResultFactory.notApplicable("Invalid position: " + localPosition);
            }

        }

        if(!(laInduction || constructorInduction || variableInduction)){
            return ResultFactory.notApplicable("Merging not allowed.");
        }

        for(int i = 0; i < localPositions.size(); i++){
            Position posi = localPositions.get(i);
            for(int j = i+1; j < localPositions.size(); j++){
                Position posj = localPositions.get(j);
                if (!posi.isIndependent(posj)){
                    return ResultFactory.notApplicable("Positions are not independent.");
                }
            }
        }

        Set<AlgebraVariable> variablesInFormula = formula.getAllVariables();
        for (Pair<Formula, Set<VariableSymbol>> pair : obligationInput.getHypothesesAsSet()) {
            Set<AlgebraVariable> vars = pair.x.getAllVariables();
            variablesInFormula.addAll(vars);
        }

        InductionScheme is = CoverSet.generateMergedInductionScheme(termsWithPosition ,
                laInduction, variablesInFormula, program, this.skipLAHypothesisHeuristic);

        List<InductionSchemeComponent> iscs = is.getInductionSchemeComponents();

        Set<TheoremProverObligation> newObligations = new LinkedHashSet<TheoremProverObligation>(
                iscs.size());

        for (InductionSchemeComponent component : iscs) {

            InductionSchemeTupel conclusion = component.getConclusion();

            List<InductionSchemeTupel> hypotheses = component.getHypotheses();

            Set<HypothesisPair> hypothesesSet;
            hypothesesSet = new LinkedHashSet<HypothesisPair>(hypotheses.size());


            AlgebraSubstitution conclusionSubstitution = conclusion.getSubstitution();

            AlgebraSubstitution hypothesisSubstitution;
            AlgebraTerm replaceTerm;
            Position replacePos;

            for (InductionSchemeTupel ist : hypotheses) {
                /*
                 * Construct step case
                 */

                hypothesisSubstitution = ist.getSubstitution();
                List<Pair<Position, AlgebraTerm>> replacement = ist.getReplacement();

                Formula hypothesis_conjecture = formula;

                try {
                    for (Pair<Position, AlgebraTerm> pair : replacement) {
                        replacePos = pair.x;
                        replaceTerm = pair.y;
                        hypothesis_conjecture = hypothesis_conjecture.replaceTermAt(replaceTerm,
                                replacePos);
                    }
                }
                catch (InvalidPositionException e) {
                    e.printStackTrace();
                }
                hypothesis_conjecture = hypothesis_conjecture.apply(hypothesisSubstitution);

                List<Equation> conditions = ist.getConditions();

                Formula hypothesis_conditions = null;
                if (conditions != null) {
                    hypothesis_conditions = And.create(conditions);
                }

                Formula hypothesis;
                if (hypothesis_conditions != null) {
                    hypothesis = Implication.create(hypothesis_conditions,
                            hypothesis_conjecture);
                }
                else {
                    hypothesis = hypothesis_conjecture;
                }

                Set<VariableSymbol> instanciableVariables = new LinkedHashSet<VariableSymbol>(
                        hypothesis.getAllVariableSymbols());

                Set<VariableSymbol> varInRange = hypothesisSubstitution
                        .getVariableSymbolsInRange();
                instanciableVariables.removeAll(varInRange);

                if(this.evaluateHypothesis){
                    if(laProgram != null){
                        hypothesis = FormulaOutermostLAEvaluationVisitor.apply(hypothesis,program);
                    }
                    else{
                        hypothesis = FormulaOutermostEvaluationVisitor.apply(hypothesis, program);
                    }
                }

                hypothesesSet.add(new HypothesisPair(hypothesis, instanciableVariables));
            }

            Formula newFormula = null;

            List<Pair<Position, AlgebraTerm>> replacement = conclusion.getReplacement();

            Formula conjecture = formula;

            try {
                for (Pair<Position, AlgebraTerm> pair : replacement) {
                    replacePos = pair.x;
                    replaceTerm = pair.y;
                    conjecture = conjecture.replaceTermAt(replaceTerm,
                            replacePos);
                }
            }
            catch (InvalidPositionException e) {
                e.printStackTrace();
            }
            conjecture = conjecture.apply(conclusionSubstitution);


            List<Equation> conditions = conclusion.getConditions();

            Formula conclusion_conditions = null;
            if (conditions != null) {
                conclusion_conditions = And.create(conditions);
            }

            if (conclusion_conditions != null) {
                newFormula = Implication.create(conclusion_conditions,
                        conjecture);
            }
            else {
                newFormula = conjecture;
            }

            TheoremProverObligation newObligation = new TheoremProverObligation(
                    newFormula, program, hypothesesSet, obligationInput);

            newObligations.add(newObligation);
        }

        InductionByAlgorithmCoverSetProof proof = new InductionByAlgorithmCoverSetProof(
                newObligations,
                termsWithPosition,
                is);

        if (obligationInput.getHypotheses().isEmpty()) {
            return ResultFactory.provedAnd(newObligations,
                    YNMImplication.EQUIVALENT, proof);
        }
        else {
            return ResultFactory.provedAnd(newObligations,
                    YNMImplication.SOUND, proof);
        }

    }

    public ArrayList<Position> parsePositions(String positionsStr) {
        StringTokenizer posTokenizer = new StringTokenizer(positionsStr, "[],", false);

        ArrayList<Position> positions = new ArrayList<Position>();

        while(posTokenizer.hasMoreTokens()){
            String position = posTokenizer.nextToken().trim();

            if(!position.equals("")){
                Position pos = Position.create(position);
                positions.add(pos);
            }
        }

        return positions;
    }

    public static class Arguments {
        public boolean evaluateHypothesis;
        public String positions;
        public boolean skipLAHypothesisHeuristic = true;
    }

}
