package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Exceptions.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.ComplexitySummary.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Transforms the RNTS into an ITS to obtain a size bound for a single function.
 * Inner function calls must already have been replaced by their size bounds
 * (by the ResultPropagation processor). Outer function calls (outside of the
 * target function) are replaced by their previously obtained size bounds
 * by this processor.
 *
 * The resulting rules are then transformed into an ITS in such a way that
 * the runtime of the ITS equals the return value of the target function.
 * For this purpose, two constructions are used:
 *
 * (a) Additive accumulator:
 *   f(x) -> 2 + f(x-1)  becomes  f(acc,x) -> f(acc+2,x-1) [weight 0]
 *   A final transition f(acc,x) -> sink() [weight acc] encodes the return value
 *   (final value of acc) as runtime complexity. Initially, acc is set to 0
 *   by an extra start rule.
 *
 * (b) Return value as weight:
 *   f(x) -> 2 + f(x-1)  becomes  f(x) -> f(x-1) [weight 2]
 *   Here, the return value is simply encoded as the cost of the ITS transition.
 *   No extra rules are necessary.
 *
 * Multiplication (e.g. f(x) -> 2*f(x)) is always handled by a multiplicative
 * accumulator (which usually results in nonlinear arithmetic in the ITS which
 * is very hard to handle for the ITS backends).
 *
 * The size bound is then obtained using an IntTrsBackend.
 *
 * @warning ResultPropagation processor must be run before this processor!
 *
 * @author mnaaf
 *
 */
public class CpxRntsSizeProcessor extends ProcessorSkeleton {

    //options
    private final IntTrsBackendSpawner.Timeouts timeouts;

    //arguments that can be passed from the strategy file
    public static class Arguments {
        //timeout for the ITS backends
        public int pubsTimeout = 3000;
        public int koatTimeout = 6000;
        public int coflocoTimeout = 4000;
    }

    @ParamsViaArgumentObject
    public CpxRntsSizeProcessor(final Arguments arguments) {
        this.timeouts = new IntTrsBackendSpawner.Timeouts();
        this.timeouts.pubs = arguments.pubsTimeout;
        this.timeouts.koat = arguments.koatTimeout;
        this.timeouts.cofloco = arguments.coflocoTimeout;
    }


    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!IntTrsBackendSpawner.anyBackendInstalled()) return false;
        if (!(obl instanceof CpxRntsProblem)) return false;
        return ((CpxRntsProblem)obl).hasTodo();
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsSizeWorker worker = new CpxRntsSizeWorker();
        Result res = worker.process(obl, oblNode, aborter, rti);
        return res;
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private class CpxRntsSizeWorker {
        private class AbstractedRule {
            List<TRSFunctionApplication> rhss = new ArrayList<TRSFunctionApplication>();
            List<SimplePolynomial> facs = new ArrayList<SimplePolynomial>();
            SimplePolynomial acc = null;
            TRSFunctionApplication lhs = null;
            ImmutableSet<Constraint> guard = null;
        }

        private CpxRntsProblem rnts = null; //used as read-only reference for helper methods
        private IntTrsBoundProofBuilder proofBuilder = null;

        //special new (fresh) names
        private TRSVariable acc = null;
        private TRSVariable fac = null;
        private String outputLoc = null;
        private String startLoc = null;

        //for rhs abstraction: maps the created indefinites to the corresponding rhs funapp
        private Map<TRSVariable,TRSFunctionApplication> indefToRhsMap = null;


        private void generateSpecialVariables() {
            FreshNameGenerator fng = new FreshNameGenerator(this.rnts.getVariables(), FreshNameGenerator.VARIABLES);
            this.acc = TRSTerm.createVariable(fng.getFreshName("acc", false));
            this.fac = TRSTerm.createVariable(fng.getFreshName("fac", false));
        }

        private void generateSpecialLocations() {
            FreshNameGenerator fng = new FreshNameGenerator(this.rnts.getDefinedSymbols(), FreshNameGenerator.VARIABLES);
            this.outputLoc = fng.getFreshName("output", false);
            this.startLoc = fng.getFreshName("start", false);
        }

        private void initializeMembers(CpxRntsProblem rnts) {
            this.rnts = rnts;
            this.indefToRhsMap.clear();
            generateSpecialLocations();
            generateSpecialVariables();
        }

        private TRSTerm inlineOuter(TRSTerm term) {
            if (term.isVariable()) return term;
            TRSFunctionApplication funapp = (TRSFunctionApplication)term;
            FunctionSymbol fun = funapp.getRootSymbol();

            //if this function has not been analyzed, replace it by an unknown to be computed
            if (rnts.isDefinedSymbol(fun) && !rnts.hasResult(fun)) {
                TRSVariable fresh = this.rnts.generateFreshVariable("indef", false);
                this.indefToRhsMap.put(fresh, funapp);
                return fresh;
            }

            //otherwise abstract arguments first
            ArrayList<TRSTerm> newArgs = new ArrayList<>();
            for (TRSTerm arg : funapp.getArguments()) {
                newArgs.add(inlineOuter(arg));
            }

            //keep arithmetic terms (integer or + or *)
            if (!rnts.isDefinedSymbol(fun)) {
                assert TermHelper.isIntArithmeticSymbol(fun);
                return TRSTerm.createFunctionApplication(fun, newArgs);
            }

            //apply the known size bound (ignore costs) for fun
            assert rnts.hasResult(fun);
            return TermHelper.applyBound(rnts, newArgs, rnts.getResult(fun).getSizePoly());
        }


        //returns the additive accumulator, fills facs with new rhss and their multiplicative accumulators
        private SimplePolynomial computeAccumulators(TRSTerm rhs, Map<TRSFunctionApplication, SimplePolynomial> facs) throws NonlinearArithmeticException {
            TRSTerm inlined = inlineOuter(rhs);
            assert CpxIntTermHelper.isIntegerTerm(inlined);

            VarPolynomial poly;
            try {
                poly = TermHelper.toVarPolynomial(inlined, this.indefToRhsMap.keySet());
            } catch (NotRepresentableAsPolynomialException e) {
                throw new NonlinearArithmeticException(rhs);
            }

            if (poly.getDegree() > 1) {
                throw new NonlinearArithmeticException(rhs);
            }

            SimplePolynomial acc = poly.getConstantPart();
            for (Entry<TRSVariable,TRSFunctionApplication> entry : this.indefToRhsMap.entrySet()) {
                SimplePolynomial fac = poly.getCoefficientPoly(entry.getKey().getName());
                if (fac != null) {
                    facs.put(this.indefToRhsMap.get(entry.getKey()), fac);
                }
            }
            return acc;
        }

        //abstracts every rule into an additive accumulator and a list of rhss and multiplicative accumulators
        private Set<AbstractedRule> abstractRules(FunctionSymbol goal) throws NonlinearArithmeticException {
            Set<RntsRule> relevantRules = DependentRules.getTodoRuleClosureFrom(goal, this.rnts);
            Set<AbstractedRule> abstractedRules = new LinkedHashSet<>();

            for (RntsRule rule : relevantRules) {
                AbstractedRule absRule = new AbstractedRule();
                TRSTerm rhs = rule.getRight();

                Map<TRSFunctionApplication,SimplePolynomial> newRhss = new LinkedHashMap<>();
                absRule.acc = computeAccumulators(rhs, newRhss);
                absRule.lhs = rule.getLeft();
                absRule.guard = rule.getConstraints();

                if (newRhss.isEmpty()) {
                    absRule.facs.add(SimplePolynomial.ONE);
                    absRule.rhss.add(TRSTerm.createFunctionApplication(FunctionSymbol.create(this.outputLoc, 0)));
                } else {
                    for (Entry<TRSFunctionApplication,SimplePolynomial> entry : newRhss.entrySet()) {
                        absRule.facs.add(entry.getValue());
                        absRule.rhss.add(entry.getKey());
                    }
                }

                assert absRule.facs.size() == absRule.rhss.size();
                abstractedRules.add(absRule);
            }
            return abstractedRules;
        }

        //the multiplicative accumulator creates nonlinear problems, slice when possible
        private boolean hasNontrivialFac(Set<AbstractedRule> abstractedRules) {
            for (AbstractedRule rule : abstractedRules) {
                for (SimplePolynomial fac : rule.facs) {
                    if (!fac.equals(SimplePolynomial.ONE)) {
                        return true;
                    }
                }
            }
            return false;
        }

        //inserts acc and fac accumulators with the given increase into rhs (if the optionals are present)
        private TRSFunctionApplication insertAccumulators(TRSFunctionApplication rhs, Optional<SimplePolynomial> optAcc, Optional<SimplePolynomial> optFac)
        {
            if (optFac.isPresent()) {
                SimplePolynomial facPol = SimplePolynomial.create(this.fac.getName());
                TRSTerm facTerm = facPol.times(optFac.get()).toTerm();
                //special case for output location, which does not need fac
                if (!rhs.getRootSymbol().getName().equals(this.outputLoc)) {
                    rhs = TermHelper.prependArguments(rhs, facTerm);
                }
            }
            if (optAcc.isPresent()) {
                SimplePolynomial accPol = SimplePolynomial.create(this.acc.getName());
                if (optFac.isPresent()) {
                    accPol = accPol.plus(SimplePolynomial.create(this.fac.getName()).times(optAcc.get()));
                } else {
                    accPol = accPol.plus(optAcc.get());
                }
                rhs = TermHelper.prependArguments(rhs, accPol.toTerm());
            }
            return rhs;
        }

        //creates rule "start(acc,fac,...) -> goal(0,1,...) | ... >= 0"
        private RntsRule makeStartRule(FunctionSymbol goal, boolean useAcc, boolean useFac) {
            ArrayList<TRSTerm> rntsArgs = new ArrayList<>();
            for (int i=0; i < goal.getArity(); ++i) {
                rntsArgs.add(TRSTerm.createVariable(rnts.getArgumentName(i)));
            }

            ArrayList<TRSTerm> lhsArgs = new ArrayList<>();
            ArrayList<TRSTerm> rhsArgs = new ArrayList<>();
            if (useAcc) {
                lhsArgs.add(this.acc);
                rhsArgs.add(CpxIntTermHelper.ZERO);
            }
            if (useFac) {
                lhsArgs.add(this.fac);
                rhsArgs.add(CpxIntTermHelper.ONE);
            }
            lhsArgs.addAll(rntsArgs);
            rhsArgs.addAll(rntsArgs);
            TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(FunctionSymbol.create(this.startLoc, lhsArgs.size()), lhsArgs);
            TRSTerm rhs = TRSTerm.createFunctionApplication(FunctionSymbol.create(goal.getName(), rhsArgs.size()), rhsArgs);

            Set<Constraint> guard = new HashSet<>();
            TRSTerm minVal = CpxIntTermHelper.getInteger(CpxRntsProblem.MIN_INT_VALUE);
            for (TRSTerm arg : rntsArgs) {
                guard.add(TermHelper.makeGreaterEqualConstraint(arg,minVal));
            }
            return RntsRule.createUnsafe(lhs, rhs, SimplePolynomial.ZERO, ImmutableCreator.create(guard));
        }

        //creates counting loop output(acc) -> output(acc-1) with cost 1
        //NOTE: output -> sink with cost "acc" is cleaner, but koat works better with the loop
        private RntsRule makeOutputRule() {
            TRSTerm rhsArg = SimplePolynomial.create(this.acc.getName()).minus(SimplePolynomial.ONE).toTerm();
            TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(FunctionSymbol.create(this.outputLoc, 1), this.acc);
            TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(FunctionSymbol.create(this.outputLoc, 1), rhsArg);
            Constraint guard = TermHelper.makeGreaterEqualConstraint(this.acc, CpxIntTermHelper.ONE);
            return RntsRule.createUnsafe(lhs, rhs, SimplePolynomial.ONE, ImmutableCreator.create(Collections.singleton(guard)));
        }

        //makes use of the additive accumulator as a variable, handles COM_n (but with a strongly asymmetric construction)
        private CpxRntsProblem applyComAccumulatorConstruction(Set<AbstractedRule> abstractedRules, FunctionSymbol goal) {
            boolean useFac = hasNontrivialFac(abstractedRules);
            Set<RntsRule> newRules = new LinkedHashSet<>();

            for (AbstractedRule rule : abstractedRules) {
                TRSFunctionApplication lhs = rule.lhs;
                if (useFac) lhs = TermHelper.prependArguments(lhs, this.fac);
                lhs = TermHelper.prependArguments(lhs, this.acc);

                List<TRSFunctionApplication> rhss = new ArrayList<>();
                for (int i=0; i < rule.rhss.size(); ++i) {
                    //check if we have to use the fac accumulator
                    Optional<SimplePolynomial> optFac = Optional.empty();
                    if (useFac) optFac = Optional.of(rule.facs.get(i));

                    //use add accumulator only on first rhs
                    Optional<SimplePolynomial> optAcc = Optional.empty();
                    if (i == 0) {
                        optAcc = Optional.of(rule.acc);
                    }

                    TRSFunctionApplication rhs = rule.rhss.get(i);
                    rhs = insertAccumulators(rhs, optAcc, optFac);

                    //set all but the first accumulator to 0
                    if (i > 0) {
                        TRSTerm zero = SimplePolynomial.ZERO.toTerm();
                        rhs = TermHelper.prependArguments(rhs, zero);
                    }
                    rhss.add(rhs);
                }

                TRSFunctionApplication rhs;
                if (rhss.size() > 1) {
                    rhs = CpxIntTermHelper.createCom(rhss);
                } else {
                    rhs = rhss.get(0);
                }

                RntsRule newRule = RntsRule.createUnsafe(lhs, rhs, SimplePolynomial.ZERO, rule.guard);
                newRules.add(newRule);
            }
            //create auxiliary rules
            newRules.add(makeOutputRule());
            RntsRule startRule = makeStartRule(goal, true, useFac);
            newRules.add(startRule);
            return this.rnts.cloneWithNewRules(ImmutableCreator.create(newRules),ImmutableCreator.create(Collections.singleton(startRule.getRootSymbol())));
        }

        //makes use of rule costs to model the additive accumulator, can handle COM_n
        private CpxRntsProblem applyCostConstruction(Set<AbstractedRule> abstractedRules, FunctionSymbol goal) {
            boolean useFac = hasNontrivialFac(abstractedRules);
            Set<RntsRule> newRules = new LinkedHashSet<>();

            for (AbstractedRule rule : abstractedRules) {
                TRSFunctionApplication lhs = rule.lhs;
                if (useFac) lhs = TermHelper.prependArguments(lhs, this.fac);

                List<TRSFunctionApplication> rhss = new ArrayList<>();
                for (int i=0; i < rule.rhss.size(); ++i) {
                    TRSFunctionApplication rhs = rule.rhss.get(i);
                    if (useFac) rhs = insertAccumulators(rhs, Optional.empty(), Optional.of(rule.facs.get(i)));
                    rhss.add(rhs);
                }

                TRSFunctionApplication rhs;
                if (rhss.size() > 1) {
                    rhs = CpxIntTermHelper.createCom(rhss);
                } else {
                    rhs = rhss.get(0);
                }

                SimplePolynomial cost = rule.acc;
                if (useFac) {
                    cost = SimplePolynomial.create(this.fac.toString()).times(cost);
                }

                RntsRule newRule = RntsRule.createUnsafe(lhs, rhs, cost, rule.guard);
                newRules.add(newRule);
            }
            //create auxiliary rules
            RntsRule startRule = makeStartRule(goal, false, useFac);
            newRules.add(startRule);
            return this.rnts.cloneWithNewRules(ImmutableCreator.create(newRules),ImmutableCreator.create(Collections.singleton(startRule.getRootSymbol())));
        }

        private CpxRntsProblem processFun(FunctionSymbol goal, CpxRntsProblem rnts, Abortion aborter) {
            //initialize global state
            assert goal != null;
            initializeMembers(rnts);

            //abstract to an ITS using accumulators for size bounds
            Set<AbstractedRule> abstracted;
            try {
                abstracted = abstractRules(goal);
            } catch (NonlinearArithmeticException e) {
                ComplexitySummary infty = ComplexitySummary.partial(CpxType.Size, ComplexityValue.infinite(), Optional.empty());
                return rnts.cloneWithUpdatedResult(goal, infty);
            }

            //choose type of construction (currently: run both and choose best result)
            CpxRntsProblem its, accumIts, costIts;

            //accumulator
            accumIts = applyComAccumulatorConstruction(abstracted, goal);
            IntTrsBackend accumSolver = IntTrsBackendSpawner.runAll(accumIts, aborter, CpxRntsSizeProcessor.this.timeouts);
            ComplexityValue accumCpx = accumSolver.getComplexity();
            Optional<SimplePolynomial> accumPol = accumSolver.getPolynomialBound();

            //rule costs
            costIts = applyCostConstruction(abstracted, goal);
            IntTrsBackend costSolver = IntTrsBackendSpawner.runAll(costIts, aborter, CpxRntsSizeProcessor.this.timeouts);
            ComplexityValue costCpx = costSolver.getComplexity();
            Optional<SimplePolynomial> costPol = costSolver.getPolynomialBound();

            //choose better complexity
            IntTrsBackend solver;
            if (TermHelper.isFirstCpxBetter(costCpx,costPol, accumCpx,accumPol)) {
                its = costIts;
                solver = costSolver; //prefer cost only when strictly better
            } else {
                its = accumIts;
                solver = accumSolver; //accumulator often produces smaller polynomial bounds
            }

            /* Heuristic for cost vs accumulator decision:
            if (hasMultipleRhss(abstracted)) {
                its = applyCostConstruction(abstracted, goal);
            } else {
                its = applyAccumulatorConstruction(abstracted, goal);
            }*/

            ComplexityValue newCpx = solver.getComplexity();
            Optional<SimplePolynomial> newPoly = solver.getPolynomialBound();

            if (newPoly.isPresent()) {
                assert !newPoly.get().containsIndefinite(this.acc.getName());
                assert !newPoly.get().containsIndefinite(this.fac.getName());
            }

            ComplexitySummary cpxres = ComplexitySummary.partial(CpxType.Size, newCpx, newPoly);
            this.proofBuilder.add(goal, cpxres, its, solver);
            return rnts.cloneWithUpdatedResult(goal, cpxres);
        }

        public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
                throws AbortionException {
            //check applicability
            CpxRntsProblem rntsObl = (CpxRntsProblem)obl;
            assert rntsObl.hasAnalysisOrder();
            assert rntsObl.hasTodo();

            //allocate global state
            this.indefToRhsMap = new LinkedHashMap<>();
            this.proofBuilder = new IntTrsBoundProofBuilder(CpxType.Size);

            //analyze all function symbols in this todo step
            for (FunctionSymbol todofun : rntsObl.getTodo()) {
                rntsObl = processFun(todofun, rntsObl, aborter);
            }
            return ResultFactory.proved(rntsObl, UpperBound.create(), proofBuilder.buildProof());
        }
    }
}
