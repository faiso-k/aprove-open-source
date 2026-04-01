package aprove.verification.complexity.LowerBounds;

import java.util.*;
import java.util.Map.*;
import java.util.stream.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Obligations.Junctors.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Rule;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class CpxTrsDecreasingLoopProcessor extends ProcessorSkeleton {

    @SuppressWarnings("serial")
    private class ExponentialLowerBoundException extends Exception {

        DecreasingLoopProof proof;

        ExponentialLowerBoundException(DecreasingLoopProof proof) {
            this.proof = proof;
        }
    }

    @SuppressWarnings("serial")
    private class InfiniteLowerBoundException extends Exception {

        InfiniteLowerBoundProof proof;

        InfiniteLowerBoundException(InfiniteLowerBoundProof proof) {
            this.proof = proof;
        }
    }

    private class Worker {

        private Abortion aborter;
        private DecreasingLoopProblem cpxTrs;
        private Map<Rule, DecreasingLoopProof> proved = new LinkedHashMap<>();

        public Worker(DecreasingLoopProblem cpxTrs, Abortion aborter) {
            this.aborter = aborter;
            this.cpxTrs = cpxTrs;
        }

        public Result process() {
            Optional<Result> res = processObligation();
            while (!res.isPresent()) {
                cpxTrs = cpxTrs.narrow(aborter);
                res = processObligation();
            }
            return res.get();
        }

        public Optional<Result> processObligation() {
            RenamingCentral renamingCentral = RenamingCentral.create(cpxTrs.getUsedNames());
            Set<Rule> done = new LinkedHashSet<>();
            Set<Rule> todo = cpxTrs.getTodo();
            for (Rule toAnalyze: todo) {
                done.add(toAnalyze);
                Rule linearToAnalyze;
                TRSFunctionApplication lhs = toAnalyze.getLeft();
                if (lhs.isLinear()) {
                    linearToAnalyze = toAnalyze;
                } else {
                    Map<TRSVariable, Integer> varCount = lhs.getVariableCount();
                    Map<TRSVariable, TRSTerm> replacementMap = new LinkedHashMap<>();
                    for (Entry<TRSVariable, Integer> e: varCount.entrySet()) {
                        if (e.getValue() > 1) {
                            TRSVariable x = e.getKey();
                            replacementMap.put(x, TRSTerm.createFunctionApplication(renamingCentral.freshSymbol(x.getName(), 0)));
                        }
                    }
                    Substitution sigma = TRSSubstitution.create(ImmutableCreator.create(replacementMap));
                    lhs = lhs.applySubstitution(sigma);
                    TRSTerm rhs = toAnalyze.getRight().applySubstitution(sigma);
                    linearToAnalyze = new Rule(lhs, rhs);
                }
                aborter.checkAbortion();
                try {
                    if (!linearToAnalyze.getRight().isVariable()) {
                        new RuleWorker(linearToAnalyze.getLeft(), (TRSFunctionApplication) linearToAnalyze.getRight()).analyze();
                        Optional<Result> res = getResult(done);
                        if (res.isPresent()) {
                            return res;
                        }
                    }
                } catch (ExponentialLowerBoundException e) {
                    return Optional.of(ResultFactory.provedWithValue(ComplexityYNM.createLower(e.proof.complexity()), e.proof));
                } catch (InfiniteLowerBoundException e) {
                    return Optional.of(ResultFactory.provedWithValue(ComplexityYNM.createLower(ComplexityValue.infinite()), e.proof));
                }
            }
            return Optional.empty();
        }

        boolean isBasic(TRSFunctionApplication t) {
            for (TRSTerm argument : t.getArguments()) {
                Set<FunctionSymbol> defSymbolsInArgument = new LinkedHashSet<>(argument.getFunctionSymbols());
                defSymbolsInArgument.retainAll(cpxTrs.getDefinedSymbols());
                if (!defSymbolsInArgument.isEmpty()) {
                    return false;
                }
            }
            return true;
        }

        private Optional<Result> getResult(Set<Rule> analyzed) {
            if (this.proved.isEmpty()) {
                return Optional.empty();
            } else {
                DecreasingLoopProof proof = this.proved.values().iterator().next();
                ComplexityValue newLowerBound = proof.complexity();
                TruthValue tv = cpxTrs.getTrs().getTruthValue();
                if (tv instanceof ComplexityYNM) {
                    ComplexityValue oldLowerBound = ((ComplexityYNM) tv).getLowerBound();
                    if (oldLowerBound.compareTo(newLowerBound) >= 0) {
                        return Optional.empty();
                    }
                }
                List<BasicObligation> todo = new ArrayList<>();
                todo.add(new ProvenLowerBound(cpxTrs.getTrs(), newLowerBound));
                todo.add(cpxTrs.nextObligation(analyzed));
                return Optional.of(ResultFactory.provedWithJunctor(todo, Junctors.BEST, LowerBound.create(), proof));
            }
        }

        private class RuleWorker {

            TRSFunctionApplication lhs;
            TRSFunctionApplication rhs;
            Map<TRSVariable, Position> lhsVarPositions = new LinkedHashMap<>();
            Set<DecreasingLoop> decreasingLoops = new LinkedHashSet<>();

            RuleWorker(TRSFunctionApplication lhs, TRSFunctionApplication rhs) {
                this.lhs = lhs;
                this.rhs = rhs;
                for (Entry<TRSVariable, List<Position>> e: lhs.getVariablePositions().entrySet()) {
                    lhsVarPositions.put(e.getKey(), e.getValue().get(0));
                }
            }

            void analyze() throws ExponentialLowerBoundException, InfiniteLowerBoundException {
                if (cpxTrs.isDerivational() || isBasic(this.lhs)) {
                    this.searchRecursiveCalls();
                    if (!decreasingLoops.isEmpty()) {
                        for (Pair<DecreasingLoop, DecreasingLoop> p: Collection_Util.getPairs(this.decreasingLoops)) {
                            Set<DecreasingLoop> loops = new LinkedHashSet<>();
                            loops.add(p.x);
                            loops.add(p.y);
                            if (this.areCompatible(loops)) {
                                this.computeExponentialResult(loops);
                                return;
                            }
                        }
                        this.computePolynomialResult(this.decreasingLoops.iterator().next());
                    }
                }
            }

            void searchRecursiveCalls() throws InfiniteLowerBoundException {
                for (Pair<Position, TRSTerm> p : this.rhs.getPositionsWithSubTerms()) {
                    Position pi = p.x;
                    TRSTerm subterm = p.y;
                    if (!subterm.isVariable()) {
                        new SubtermWorker((TRSFunctionApplication) subterm, pi).analyze();
                    }
                }
            }

            void computePolynomialResult(DecreasingLoop loop) {
                Rule rule = this.rule();
                DecreasingLoopProof proof = new DecreasingLoopProof(loop);
                this.noteProof(rule, proof);
            }

            void noteProof(Rule rule, DecreasingLoopProof proof) {
                if (!proved.containsKey(rule)) {
                    proved.put(rule, proof);
                }
            }

            void computeExponentialResult(Set<DecreasingLoop> loops) throws ExponentialLowerBoundException {
                assert loops.size() > 1;
                DecreasingLoopProof proof = new DecreasingLoopProof(loops);
                throw new ExponentialLowerBoundException(proof);
            }

            Rule rule() {
                return new Rule(this.lhs, this.rhs);
            }

            boolean areCompatible(Set<DecreasingLoop> decreasingLoops) {
                Set<TRSSubstitution> thetas = decreasingLoops.stream().map(loop -> loop.theta()).collect(Collectors.toSet());
                assert !thetas.contains(null);
                if (!this.commutes(thetas)) {
                    return false;
                }
                Set<Position> positions = decreasingLoops.stream().map(loop -> loop.pi).collect(Collectors.toSet());
                if (!this.areIndependent(positions)) {
                    return false;
                }
                Set<TRSVariable> varsInDomain = thetas.stream().flatMap(theta -> theta.getDomain().stream()).collect(Collectors.toSet());
                Set<TRSVariable> varsInCodomain = thetas.stream().flatMap(theta -> theta.getVariablesInCodomain().stream()).collect(Collectors.toSet());
                Set<TRSSubstitution> sigmas = decreasingLoops.stream().map(loop -> loop.sigma()).collect(Collectors.toSet());
                assert !sigmas.contains(null);
                for (TRSSubstitution sigma: sigmas) {
                    if (!Collection_Util.areDisjoint(sigma.getDomain(), varsInCodomain)) {
                        return false;
                    }
                    for (TRSTerm t: sigma.getCodomain()) {
                        Set<TRSVariable> intersection = Collection_Util.intersection(t.getVariables(), varsInDomain);
                        if (intersection.size() > 1) {
                            return false;
                        }
                    }
                }
                return true;
            }


            boolean commutes(Set<TRSSubstitution> substitutions) {
                for (Pair<TRSSubstitution, TRSSubstitution> p: Collection_Util.getPairs(substitutions)) {
                    if (!Utils.commutative(p.x, p.y)) {
                        return false;
                    }
                }
                return true;
            }

            boolean areIndependent(Set<Position> positions) {
                for (Pair<Position, Position> p: Collection_Util.getPairs(positions)) {
                    if (!p.x.isIndependent(p.y)) {
                        return false;
                    }
                }
                return true;
            }

            class SubtermWorker {

                TRSFunctionApplication subterm;
                Position pi;
                Map<TRSVariable, Position> toAbstract = new LinkedHashMap<>();
                TRSTerm abstractedLhs;
                Map<TRSVariable, List<Position>> varPositions;

                SubtermWorker(TRSFunctionApplication subterm, Position pi) {
                    this.subterm = subterm;
                    this.pi = pi;
                    this.abstractedLhs = lhs;
                    this.varPositions = subterm.getVariablePositions();
                }

                void analyze() throws InfiniteLowerBoundException {
                    aborter.checkAbortion();
                    this.abstractLhs();
                    TRSSubstitution sigma = this.abstractedLhs.getMatcher(this.subterm);
                    if (sigma != null) {
                        if (this.abstractedLhs.equals(lhs)) {
                            throw new InfiniteLowerBoundException(new InfiniteLowerBoundProof(new DecreasingLoop(lhs, this.abstractedLhs, rhs, this.pi)));
                        }
                        this.noteDecreasingLoop();
                    }
                }

                void abstractLhs() {
                    for (TRSVariable x : subterm.getVariables()) {
                        this.tryToAbstractVariable(x, lhsVarPositions.get(x));
                    }
                }

                void tryToAbstractVariable(TRSVariable x, Position lhsPositionOfX) {
                    for (Position rhsPositionOfX : this.varPositions.get(x)) {
                        if (this.tryToAbstractOccurrenceOfVariable(x, lhsPositionOfX, rhsPositionOfX)) {
                            return;
                        }
                    }
                }

                boolean tryToAbstractOccurrenceOfVariable(TRSVariable x, Position lhsPositionOfX, Position rhsPositionOfX) {
                    boolean abstractedVariable = false;
                    Set<Position> allPositions = new LinkedHashSet<>(this.toAbstract.values());
                    allPositions.add(rhsPositionOfX);
                    if (!rhsPositionOfX.equals(lhsPositionOfX) && rhsPositionOfX.isPrefixOf(lhsPositionOfX)
                            && areIndependent(allPositions)) {
                        this.toAbstract.put(x, rhsPositionOfX);
                        this.abstractedLhs = this.abstractedLhs.replaceAt(rhsPositionOfX, x);
                        abstractedVariable = true;
                    }
                    return abstractedVariable;
                }

                void noteDecreasingLoop() {
                    decreasingLoops.add(new DecreasingLoop(lhs, this.abstractedLhs, rhs, this.pi));
                }

            }
        }
    }


    static private class DecreasingLoop implements Exportable {
        TRSFunctionApplication lhs;
        TRSTerm abstractedLhs;
        TRSFunctionApplication rhs;
        Position pi;

        public DecreasingLoop(TRSFunctionApplication lhs, TRSTerm abstractedLhs, TRSFunctionApplication rhs, Position pi) {
            super();
            this.lhs = lhs;
            this.abstractedLhs = abstractedLhs;
            this.rhs = rhs;
            this.pi = pi;
        }

        TRSSubstitution sigma() {
            return this.abstractedLhs.getMatcher(this.rhs.getSubterm(this.pi));
        }

        TRSSubstitution theta() {
            return this.abstractedLhs.getMatcher(this.lhs);
        }

        @Override
        public String export(Export_Util eu) {
            String res = eu.escape("The rewrite sequence") + eu.newline();
            res += eu.export(this.lhs) + eu.appSpace()
                   + eu.rightarrow()
                   + eu.sup(eu.escape("+"))
                   + eu.appSpace()
                   + this.rhs.export(eu)
                   + eu.newline();
            res += eu.escape("gives rise to a decreasing loop by considering the right hand sides subterm at position ")
                   + this.pi.export(eu) + eu.escape(".") + eu.newline();
            res += eu.escape("The pumping substitution is ") + this.theta().export(eu) + eu.escape(".") + eu.newline();
            res += eu.escape("The result substitution is ") + this.sigma().export(eu) + eu.escape(".") + eu.newline();
            return res;
        }

    }

    static class InfiniteLowerBoundProof extends DefaultProof {

        DecreasingLoop loop;

        InfiniteLowerBoundProof(DecreasingLoop loop) {
            this.loop = loop;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res = o.escape("The following loop proves infinite runtime complexity:") + o.newline();
            res += this.loop.export(o) + o.newline();
            return res;
        }

    }

    static private class DecreasingLoopProof extends DefaultProof {

        Set<DecreasingLoop> loops;

        DecreasingLoopProof(DecreasingLoop loop) {
            this.loops = Collections.singleton(loop);
        }

        public ComplexityValue complexity() {
            if (this.loops.size() == 1) {
                return ComplexityValue.linear();
            } else {
                return ComplexityValue.exponential();
            }
        }

        DecreasingLoopProof(Set<DecreasingLoop> loops) {
            this.loops = loops;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("The following loop(s) give(s) rise to the lower bound ")
                         + this.complexity().export(o, o.Omega()) + o.escape(":") + o.newline());
            for (DecreasingLoop loop : this.loops) {
                sb.append(loop.export(o) + o.newline());
            }
            return sb.toString();
        }

    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) {
        return new Worker((DecreasingLoopProblem) obl, aborter).process();
    }

    @Override
    public boolean isApplicable(BasicObligation origObl) {
        if (!(origObl instanceof DecreasingLoopProblem)) {
            return false;
        }
        DecreasingLoopProblem obl = (DecreasingLoopProblem) origObl;
        return (!obl.isInnermost() || obl.STerminates()) && Options.certifier == Certifier.NONE;
    }

}
