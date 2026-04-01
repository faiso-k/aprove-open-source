/*
 * Created on Dec 5, 2004
 */
package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TheoremProverProcedures.Induction.*;

/**
 * @author rabe
 */
public class INDFMLHeuristicProcessor extends TheoremProverProcessor {

    public static final boolean useAll = true;

    private static final boolean DEBUG_POSITIONS = Globals.DEBUG_DICKMEIS && false;

    protected static enum Techniques {
        Both, InductionByDataStructure, InductionByAlgorithm;
    }

    protected final Techniques techniques;

    protected boolean useCoverSets;

    protected final boolean merging;

    protected final boolean skipLAHypothesisHeuristic;

    protected final boolean evaluateHypothesis;

    protected final boolean looseRestrictions;

    @ParamsViaArgumentObject
    public INDFMLHeuristicProcessor(Arguments arguments) {
        this.techniques = Techniques.valueOf(arguments.techniques);
        this.useCoverSets = arguments.useCoverSets;
        this.merging = arguments.merging;
        this.skipLAHypothesisHeuristic =arguments.skipLAHypothesisHeuristic;
        this.evaluateHypothesis = arguments.evaluateHypothesis;
        this.looseRestrictions = arguments.looseRestrictions;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        TreeMap<Integer,List<UserStrategy>> strategiesToUse = new TreeMap<Integer,List<UserStrategy>>();

        Formula formula = obligationInput.getFormula();

        // get all modifiable positions in formula
        Set<Position> modifiablePositions = formula.getAllModifiablePositions(obligationInput.getProgram());

        // get all all functionsymbols that could be used by induction by algorithm
        Set<DefFunctionSymbol> candidates  = this.getCandidates(obligationInput.getProgram());

        Program program = obligationInput.getProgram();
        LAProgramProperties laProgram = program.laProgramProperties;

        /*
         * if someone checks use coversets and LA-stuff, but the laProgramProperties are not set,
         * then assume the coversets will not be usable.
         */
        if(this.useCoverSets){
            this.useCoverSets = (laProgram != null);
        }

        if(this.techniques != Techniques.InductionByDataStructure && this.useCoverSets){
            // if laProgram is null here, the whole thing will crash!
            List<Position> positions = LAInductionPositionGetter.apply(formula, laProgram);
            Collections.sort(positions);

            // delete subpositions
            for(int i = 0; i < positions.size()-1; i++){
                Position pos1 = positions.get(i);
                Position pos2 = positions.get(i+1);
                boolean isSubPosition = pos2.isSubPosition(pos1);
                if (isSubPosition){
                    positions.remove(i+1);
                    i--;
                }
            }

            positions.retainAll(modifiablePositions);

            boolean laInduction = true;
            boolean constructorInduction = true;
            boolean variableInduction = true;

            List<Position> laPositions = new ArrayList<Position>(positions.size());
            List<Position> constructorPositions = new ArrayList<Position>(positions.size());
            List<Position> variablePositions = new ArrayList<Position>(positions.size());

            for (Position localPosition : positions) {

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
                            if (disjunct && term instanceof AlgebraVariable) {
                                AlgebraVariable var = (AlgebraVariable) term;

                                if(disjunctVars.contains(var)){
                                    // not disjunct
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

                        if(laInduction){
                            laPositions.add(localPosition);
                        }
                        if(constructorInduction){
                            constructorPositions.add(localPosition);
                        }
                        if(variableInduction){
                            variablePositions.add(localPosition);
                        }
                    }
                }
                catch (Exception e) {
                    return ResultFactory.notApplicable("Invalid position: " + localPosition);
                }

            }


            if (INDFMLHeuristicProcessor.DEBUG_POSITIONS){
                System.out.println(positions);

                for (Position position : positions) {

                    TermOrFormula termOrFormula=null;
                    try {
                        termOrFormula = formula.getSubPart(position);
                    }
                    catch (InvalidPositionException e) {
                    }
                    Set<AlgebraVariable> vars = ((AlgebraTerm) termOrFormula).getVars();

                    System.out.println(position);
                    System.out.println(termOrFormula);
                    System.out.println(vars);
                }

                System.out.println("\n\n");
            }

            if(laInduction && !laPositions.isEmpty()){
                if(!this.merging){
                    Position pos = laPositions.get(0);
                    laPositions.clear();
                    laPositions.add(pos);
                }

                UserStrategy suggestedStrategy =
                    TheoremProverProcessorFactory.getInductionByAlgorithmCoverSet(
                            laPositions, this.skipLAHypothesisHeuristic, this.evaluateHypothesis, true);
                return ResultFactory.justANewStrategy(suggestedStrategy.getExecutableStrategy(obligationNode,rti));
            }

            if(constructorInduction && constructorPositions.size() > 0){
                if(!this.merging){
                    Position pos = constructorPositions.get(0);
                    constructorPositions.clear();
                    constructorPositions.add(pos);
                }

                UserStrategy suggestedStrategy =
                    TheoremProverProcessorFactory.getInductionByAlgorithmCoverSet(
                            constructorPositions, this.skipLAHypothesisHeuristic, this.evaluateHypothesis, true);
                return ResultFactory.justANewStrategy(suggestedStrategy.getExecutableStrategy(obligationNode,rti));
            }

            if(variableInduction && variablePositions.size() > 0){
                if(!this.merging){
                    Position pos = variablePositions.get(0);
                    variablePositions.clear();
                    variablePositions.add(pos);
                }

                UserStrategy suggestedStrategy =
                    TheoremProverProcessorFactory.getInductionByAlgorithmCoverSet(
                            variablePositions, this.skipLAHypothesisHeuristic, this.evaluateHypothesis, true);
                return ResultFactory.justANewStrategy(suggestedStrategy.getExecutableStrategy(obligationNode,rti));
            }

        }


        if(INDFMLHeuristicProcessor.this.techniques != Techniques.InductionByDataStructure) {

            // check all subparts of the given formula for algorithm containing a modifiable position
            outer:for(Map.Entry<TermOrFormula,List<Position>> entry : formula.getAllSubFormulasAndTermsWithPosition().entrySet()) {

                if( entry.getKey().isTerm() ) {

                    AlgebraTerm term = (AlgebraTerm)entry.getKey();

                    // check if it is a function application with pairwise different
                    // variables
                    List<VariableSymbol> variablesFound;

                    if(!term.isVariable() && !term.isConstructorTerm()) {

                        // get function application and its arguments
                        AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)term;

                        // check if functionsymbol could be used for induction by algorithm
                        if(!candidates.contains(functionApplication.getSymbol())) {
                                continue outer;
                        }

                        List<AlgebraTerm> arguments = functionApplication.getArguments();

                        // check for pairwise different variables in function application
                        variablesFound = new Vector<VariableSymbol>();
                        for(AlgebraTerm argument  : arguments) {

                            if(argument.isVariable()) {

                                if(variablesFound.contains(argument.getSymbol())) {
                                    continue outer;
                                } else {
                                    variablesFound.add(((AlgebraVariable)argument).getVariableSymbol());
                                }

                            } else {
                                continue outer;
                            }

                        }

                        // quickfix for the member example
                        // if there is a subterm f(x) at non-modifiable position
                        // having only one variable as argument
                        // then do induction over f
                        if (!this.looseRestrictions) {
                            if (variablesFound.size() == 1 && variablesFound.containsAll(formula.getAllVariableSymbols())) {
                                UserStrategy suggestedStrategy = TheoremProverProcessorFactory.getInductionByAlgorithm(functionApplication,
                                        true);
                                // new Solve( new Sequence(TheoremProverProcessorFactory.getInductionByAlgorithm(
                                //functionApplication,true),"main",false));
                                if (strategiesToUse.isEmpty() || INDFMLHeuristicProcessor.useAll) {
                                    int key = 1;
                                    if (strategiesToUse.containsKey(key)) {
                                        strategiesToUse.get(key).add(suggestedStrategy);
                                    }
                                    else {
                                        List<UserStrategy> listOfStrategies = new Vector<UserStrategy>();
                                        listOfStrategies.add(suggestedStrategy);
                                        strategiesToUse.put(key, listOfStrategies);
                                    }
                                }

                            }
                        }


                        // check if term comes from a modifiable positions
                        for (Position position : entry.getValue()) {

                            // Ignore heuristic if looseRestrictions is set
                            if (this.looseRestrictions || modifiablePositions.contains(position)) {

                                UserStrategy suggestedStrategy;

                                suggestedStrategy = TheoremProverProcessorFactory.getInductionByAlgorithm(functionApplication,true);


                                int key = this.calculateKey(formula,modifiablePositions,term);
                                if(strategiesToUse.containsKey(key)) {
                                    strategiesToUse.get(key).add(suggestedStrategy);
                                }else{
                                    List<UserStrategy> listOfStrategies = new Vector<UserStrategy>();
                                    listOfStrategies.add(suggestedStrategy);
                                    strategiesToUse.put(key,listOfStrategies);
                                }

                                break;
                            }

                        }

                    }

                }

            }

        }

        if(INDFMLHeuristicProcessor.this.techniques != Techniques.InductionByAlgorithm) {

            // check all subparts of the given formula for a variable, which occures at a modifiable position
            for(Map.Entry<TermOrFormula,List<Position>> entry : formula.getAllSubFormulasAndTermsWithPosition().entrySet()) {

                if(entry.getKey().isTerm()) {

                    AlgebraTerm term = (AlgebraTerm) entry.getKey();

                    if(term.isVariable()) {

                        for(Position position : entry.getValue() ){

                            // Ignore heuristic
                            if(this.looseRestrictions || modifiablePositions.contains(position)) {

                                UserStrategy suggestedStrategy = TheoremProverProcessorFactory.getInductionByDataStructure((AlgebraVariable)term,true);
//                                    new Solve( new Sequence(TheoremProverProcessorFactory.
//                                        getInductionByDataStructure((Variable)term,true),"main",false));

                                int key = 1;
                                if(strategiesToUse.containsKey(key)) {
                                    strategiesToUse.get(key).add(suggestedStrategy);
                                }else{
                                    List<UserStrategy> listOfStrategies = new Vector<UserStrategy>();
                                    listOfStrategies.add(suggestedStrategy);
                                    strategiesToUse.put(key,listOfStrategies);
                                }

                                break;
                            }

                        }

                    } else {
                        continue;
                    }
                }
            }

        }

        if(!strategiesToUse.isEmpty()) {
            return ResultFactory.justANewStrategy(strategiesToUse.get(strategiesToUse.lastKey()).get(0).getExecutableStrategy(obligationNode,rti));
        }else{
            return ResultFactory.unsuccessful();
        }
    }

    protected Set<DefFunctionSymbol> getCandidates(Program program) {

        // Get all defined functionsymbols
        Set<DefFunctionSymbol> originalFunctionSymbols = new LinkedHashSet<DefFunctionSymbol>(
                program.getDefFunctionSymbols());

        // Remove all Functionsymbols which are not directly recursive
        Iterator<DefFunctionSymbol> iterator = originalFunctionSymbols.iterator();
        outer:    while(iterator.hasNext()) {

            DefFunctionSymbol defFunctionSymbol = iterator.next();

            for(Rule rule : program.getRules(defFunctionSymbol)) {
                    if(rule.getRight().getFunctionSymbols().contains(defFunctionSymbol)) {
                        continue outer;
                    }
            }

            iterator.remove();

            }

        return originalFunctionSymbols;

    }

    protected int calculateKey(Formula formula, Set<Position> modifiablePositions, AlgebraTerm candidate) {

        Map<AlgebraVariable,List<Position>> variablesWithPosition = GetAllSubPartsOfClassWithPosition.apply(formula,AlgebraVariable.class);

        // remove all variable, which does not occure in modifiable positions
        Iterator<Map.Entry<AlgebraVariable,List<Position>>> iterator = variablesWithPosition.entrySet().iterator();
        outer :while(iterator.hasNext()) {
            Map.Entry<AlgebraVariable,List<Position>> entry = iterator.next();
            for(Position modifiablePosition : modifiablePositions) {
                if(entry.getValue().contains(modifiablePosition)) {
                    continue outer;
                }
            }
            iterator.remove();
        }

        // remove all variables, which would not be instantiated by the induction scheme suggested
        // by the candidate
        variablesWithPosition.keySet().retainAll(candidate.getVars());

        return variablesWithPosition.size();
    }

    public static class Arguments {
        public String techniques;
        public boolean useCoverSets;
        public boolean merging;
        public boolean skipLAHypothesisHeuristic;
        public boolean evaluateHypothesis;
        public boolean looseRestrictions;
    }

}
