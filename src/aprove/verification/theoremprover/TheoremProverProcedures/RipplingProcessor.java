/*
 * Created on 28.09.2004
 */
package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.DifferenceUnification.*;
import aprove.verification.oldframework.LemmaDatabase.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Implication;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Rippling.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;


/**
 * @author rabe
 */
public class RipplingProcessor extends TheoremProverProcessor {

    public static enum Direction {Out, In};
    private final Direction directionToUse;

    @ParamsViaArguments("Direction")
    public RipplingProcessor(String direction) {
        this.directionToUse = this.parseDirection(direction);
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput, BasicObligationNode obligationNode, Abortion aborter,
                RuntimeInformation rti) throws AbortionException {

        Formula formula = obligationInput.getFormula();

        TreeMap<Integer,Set<Position>> hypothesesRanking =
            new TreeMap<Integer,Set<Position>>();

        for(Pair<Formula,Set<VariableSymbol>> hypothesis : obligationInput.getInductionHypothesis()) {
            try {
                Set<Set<Position>> candidates = GroundDifferenceMatching.apply(formula, hypothesis.x);
                for(Set<Position> candidate : candidates) {
                    hypothesesRanking.put(candidate.size(), candidate);
                }
            }catch(DifferenceUnificationException e) {}
        }

        if(hypothesesRanking.isEmpty()) {
            return ResultFactory.notApplicable();
        }

        Formula bestCandidate;

        if(this.directionToUse == Direction.Out) {
            bestCandidate = GenerateAnnotatedFormulaVisitor.apply(formula, obligationInput.getProgram(),
                    new LinkedHashSet<Position>(), hypothesesRanking.get(hypothesesRanking.firstKey()));
        }else{
            bestCandidate = GenerateAnnotatedFormulaVisitor.apply(formula, obligationInput.getProgram(),
                    hypothesesRanking.get(hypothesesRanking.firstKey()), new LinkedHashSet<Position>());
        }

        Set<PairOfTerms> pairs = new LinkedHashSet<PairOfTerms>();
        pairs.addAll(LemmaDatabaseFactory.getLemmmaDatabase().getAllEquations());
        pairs.addAll(this.getAllUnconditionalRules(obligationInput.getProgram()));

        Pair<Formula,Set<WaveRule>> result = RipplingVisitor.apply(bestCandidate, pairs, obligationInput.getProgram());

        if(result.x.erase().equals(formula)) {
            return ResultFactory.notApplicable();
        }

        TheoremProverObligation theoremProverObligation = new TheoremProverObligation(result.x.erase(), obligationInput);
        return ResultFactory.proved(theoremProverObligation,YNMImplication.EQUIVALENT,new RipplingProof(this.directionToUse,obligationInput.getFormula(),result.x.erase(),
                result.y,bestCandidate));
    }

    public Direction parseDirection(String direction) {
        if(direction.equals("In")) {
            return Direction.In;
        }else{
            return Direction.Out;
        }
    }

    public Set<PairOfTerms> getAllUnconditionalRules(Program program) {
        Set<PairOfTerms> returnValue = new LinkedHashSet<PairOfTerms>();
        for(Rule rule: program.getRules()) {
            if(rule.getConds().isEmpty()) {
                returnValue.add(rule);
            }
        }
        return returnValue;
    }

    private static class RipplingVisitor implements CoarseGrainedTermVisitor<AlgebraTerm>, FineFormulaVisitor<Formula> {

        private enum Position {Skeleton,WaveFront};

        private Program program;

        private Set<WaveRule> usedRules;

        private Map<SyntacticFunctionSymbol,Set<Rule>> functionRuleMapping;
        private Map<Rule,Set<WaveRule>> ruleWaveRuleMapping;

        public static Pair<Formula,Set<WaveRule>> apply(Formula formula, Set<PairOfTerms> equations, Program program) {
            RipplingVisitor ripplingVisitor = new RipplingVisitor(equations,program);
            return new Pair<Formula,Set<WaveRule>>((Formula)formula.apply(ripplingVisitor),ripplingVisitor.usedRules);
        }

        private RipplingVisitor(Set<PairOfTerms> equations, Program program) {

            this.program = program;

            this.usedRules              = new LinkedHashSet<WaveRule>();
            this.functionRuleMapping = new LinkedHashMap<SyntacticFunctionSymbol,Set<Rule>>();
            this.ruleWaveRuleMapping = new LinkedHashMap<Rule,Set<WaveRule>>();

            for(PairOfTerms equation : equations) {

                Symbol leftSymbol  = equation.getLeft().getSymbol();
                Symbol rightSymbol = equation.getRight().getSymbol();

                if(!(leftSymbol instanceof VariableSymbol)) {
                    if(this.functionRuleMapping.containsKey(leftSymbol)){
                        this.functionRuleMapping.get(leftSymbol).add(Rule.create(equation.getLeft(),equation.getRight()));
                    }else{
                        LinkedHashSet<Rule> rules = new LinkedHashSet<Rule>();
                        rules.add(Rule.create(equation.getLeft(), equation.getRight()));

                        this.functionRuleMapping.put((SyntacticFunctionSymbol)leftSymbol,rules);
                    }
                }

                if(!(rightSymbol instanceof VariableSymbol)) {
                    if(this.functionRuleMapping.containsKey(rightSymbol)) {
                        this.functionRuleMapping.get(rightSymbol).add(Rule.create(equation.getRight(), equation.getLeft()));
                    }else{
                        LinkedHashSet<Rule> rules = new LinkedHashSet<Rule>();
                        rules.add(Rule.create(equation.getRight(), equation.getLeft()));

                        this.functionRuleMapping.put((SyntacticFunctionSymbol)rightSymbol,rules);
                    }
                }

            }
        }

        @Override
        public Formula caseEquation(Equation eqFormula) {
            return Equation.create((AlgebraTerm)eqFormula.getLeft().apply(this), (AlgebraTerm)eqFormula.getRight().apply(this));
        }

        @Override
        public Formula caseAnd(And andFormula) {
            return And.create(andFormula.getLeft().apply(this), andFormula.getRight().apply(this));
        }

        @Override
        public Formula caseEquivalence(Equivalence equivFormula) {
            return Equivalence.create(equivFormula.getLeft().apply(this), equivFormula.getRight().apply(this));
        }

        @Override
        public Formula caseImplication(Implication implFormula) {
            return Implication.create(implFormula.getLeft().apply(this), implFormula.getRight().apply(this));
        }

        @Override
        public Formula caseNot(Not notFormula) {
            return Not.create(notFormula.getLeft().apply(this));
        }

        @Override
        public Formula caseOr(Or orFormula) {
            return Or.create(orFormula.getLeft().apply(this), orFormula.getRight().apply(this));
        }

        @Override
        public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
            return truthvalFormula.deepcopy();
        }

        @Override
        public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication f) {

            List<AlgebraTerm> newArguments = new Vector<AlgebraTerm>();

            for(AlgebraTerm argument : f.getArguments()) {
                newArguments.add(argument.apply(this));
            }

            AlgebraTerm newTerm = AlgebraFunctionApplication.create(f.getFunctionSymbol(), newArguments);

            if(!(f.getFunctionSymbol() instanceof WaveHole)) {
                AlgebraFunctionApplication erasedTerm = (AlgebraFunctionApplication)newTerm.erase();

                Set<Rule> rules = this.functionRuleMapping.get(erasedTerm.getFunctionSymbol());

                if(rules == null) {
                    return newTerm;
                }

                for(Rule rule : rules) {
                    try {

                        rule.getLeft().matches(erasedTerm);

                        if(!this.ruleWaveRuleMapping.containsKey(rule)) {

                            Set<WaveRule> waveRules = WaveRuleParser.generateWaveRules(rule, this.program);
                            this.ruleWaveRuleMapping.put(rule, waveRules);

                            for(WaveRule waveRule : waveRules) {
                                try {
                                    AnnotatedSubstitution substitution = this.annotatedMatching(waveRule.getLeft(),newTerm);
                                    this.usedRules.add(waveRule);

                                    newTerm = this.apply(waveRule.getRight(),substitution,false).apply(this);
                                    break;
                                }catch(UnificationException e) {}
                            }
                        }else{
                            for(WaveRule waveRule : this.ruleWaveRuleMapping.get(rule)) {
                                try {
                                    AnnotatedSubstitution substitution = this.annotatedMatching(waveRule.getLeft(),newTerm);
                                    this.usedRules.add(waveRule);

                                    newTerm = this.apply(waveRule.getRight(),substitution,false).apply(this);
                                    break;
                                }catch(UnificationException e) {}
                            }
                        }

                    }
                    catch(UnificationException e) {}
                    catch(DifferenceUnificationException e){}

                }

            }

            return newTerm;
        }

        @Override
        public AlgebraTerm caseVariable(AlgebraVariable v) {
            return v.deepcopy();
        }


        public AlgebraTerm apply(AlgebraTerm term, AnnotatedSubstitution substitution, boolean erase) {

            if(term.isVariable()) {
                if(substitution.containsKey(term.getSymbol())) {
                    AlgebraTerm newTerm = substitution.get((VariableSymbol)term.getSymbol());
                    return erase ? newTerm.erase(): newTerm.deepcopy();
                }else{
                    return term.deepcopy();
                }
            }else{
                if(term.isMetaFunctionApplication()) {

                    MetaFunctionApplication metaFunctionApplication = (MetaFunctionApplication)term;

                    List<AlgebraTerm> newArguments = new Vector<AlgebraTerm>();

                    if(metaFunctionApplication.getMetaFunctionSymbol().isWaveFrontIn() ||
                       metaFunctionApplication.getMetaFunctionSymbol().isWaveFrontOut()) {

                        for(AlgebraTerm argument : metaFunctionApplication.getArguments()) {
                            if(argument.isMetaFunctionApplication()) {
                                newArguments.add(this.apply(argument, substitution,false));
                            }else{
                                newArguments.add(this.apply(argument,substitution,true));
                            }
                        }

                    }else{
                        for(AlgebraTerm argument : metaFunctionApplication.getArguments()) {
                            newArguments.add(this.apply(argument, substitution, erase));
                        }
                    }

                    return AlgebraFunctionApplication.create(metaFunctionApplication.getFunctionSymbol(),newArguments);

                }

                AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)term;

                List<AlgebraTerm> newArguments = new Vector<AlgebraTerm>();

                for(AlgebraTerm argument : functionApplication.getArguments()) {
                    newArguments.add(this.apply(argument,substitution,erase));
                }

                return AlgebraFunctionApplication.create(functionApplication.getFunctionSymbol(),newArguments);

            }

        }

        private AnnotatedSubstitution annotatedMatching(AlgebraTerm s, AlgebraTerm t) throws UnificationException {
            return this.annotatedMatching(s,t, new AnnotatedSubstitution(),Position.Skeleton);
        }

        private AnnotatedSubstitution annotatedMatching(AlgebraTerm s, AlgebraTerm t, AnnotatedSubstitution substitution, RipplingVisitor. Position position ) throws UnificationException {

            if(s.isVariable()) {
                VariableSymbol variableSymbol = (VariableSymbol)s.getSymbol();
                if(substitution.get(variableSymbol)!=null) {
                    if(position != substitution.getSource(variableSymbol)) {
                        if(position == Position.Skeleton){
                            if(!t.equals(EraseAnnotatedFormulaVisitor.apply(substitution.get(variableSymbol))) ){
                                throw new MatchFailureException("",s,t);
                            }else{
                                substitution.put(variableSymbol,position,t);
                            }
                        }else{
                            if(!EraseAnnotatedFormulaVisitor.apply(t).equals(substitution.get(variableSymbol))) {
                                throw new MatchFailureException("",s,t);
                            }
                        }
                    }else{
                        if(!substitution.get(variableSymbol).equals(t)) {
                            throw new MatchFailureException("",s,t);
                        }
                    }
                }else{
                    substitution.put(variableSymbol, position, t);
                }
            }else if(t.isVariable()){
                throw new MatchFailureException("",s,t);
            }else{
                if(s.getSymbol().equals(t.getSymbol())) {
                    AlgebraFunctionApplication functionApplication = (AlgebraFunctionApplication)s;
                    if(functionApplication.isMetaFunctionApplication()) {
                        MetaFunctionSymbol metaFunctionSymbol = ((MetaFunctionApplication)functionApplication).getMetaFunctionSymbol();
                        if(metaFunctionSymbol.isWaveFrontIn() || metaFunctionSymbol.isWaveFrontOut()) {
                            this.annotatedMatching(s.getArgument(0),t.getArgument(0), substitution, Position.WaveFront);
                        }else{
                            this.annotatedMatching(s.getArgument(0),t.getArgument(0), substitution, Position.Skeleton);
                        }
                    }else{
                        for(int i=0;i < functionApplication.getFunctionSymbol().getArity(); i++) {
                            this.annotatedMatching(s.getArgument(i),t.getArgument(i),substitution,position);
                        }
                    }
                }else{
                    throw new MatchFailureException("",s,t);
                }
            }

            return substitution;
        }

        private static class AnnotatedSubstitution extends LinkedHashMap<VariableSymbol,AlgebraTerm> {

            private LinkedHashMap<VariableSymbol,RipplingVisitor.Position> source;

            public AnnotatedSubstitution() {
                super();
                this.source = new LinkedHashMap<VariableSymbol,RipplingVisitor.Position>();
            }

            public void put(VariableSymbol variableSymbol, RipplingVisitor.Position source, AlgebraTerm value ) {
                this.source.put(variableSymbol,source);
                this.put(variableSymbol, value);
            }

            public RipplingVisitor.Position getSource(VariableSymbol variableSymbol) {
                return this.source.get(variableSymbol);
            }

        }

    }

}
