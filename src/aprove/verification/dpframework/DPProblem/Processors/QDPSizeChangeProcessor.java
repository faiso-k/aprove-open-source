package aprove.verification.dpframework.DPProblem.Processors;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SAT.PLEncoders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.Interpretation;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;
import immutables.*;

/**
 * QDP Size-Change processor.
 *
 * @author R. Thiemann
 * @version $Id$
 */
public class QDPSizeChangeProcessor extends QDPProblemProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPSizeChangeProcessor");

    private final Engine engine;

    private final boolean subterm;    // use subterm criterion; if true, then other options have no impact!

    private final SolverFactory factory; // if this is set and subterm is not, the other options are ignored

    private final boolean mergeMutual;
    private final int usableArgumentsRestriction;   // Maximal size of D_P (-1 will be changed to maxInt => no limit)
    private final int afsRestriction; // Maximal nr of symbols to filter in SCP (-1 will be changed to maxInt => no limit)
    private final BigInteger range;

    @ParamsViaArgumentObject
    public QDPSizeChangeProcessor(final Arguments arguments) {
        this.engine = arguments.engine;
        this.subterm = arguments.subterm;
        this.factory = arguments.order;
        this.mergeMutual = arguments.mergeMutual;
        this.range = BigInteger.valueOf(arguments.Range);

        this.usableArgumentsRestriction =
            this.parseUsableArgumentsRestriction(arguments.usableArgumentsRestriction);
        this.afsRestriction =
            this.parseAfsRestriction(arguments.afsRestriction);
    }

    /**
     * approximates whether there may be a possible connection
     * between s and t, i.e. there may possibly be an afs pi such
     * that pi(s) >=_emb pi(t).
     * (current impl. checks whether some variable of function
     * symbol on the right also occurs on the left hand side,
     * then both parts can possibly be filtered to that
     * variable/function symbol (as constant)
     * @param s
     * @param t
     * @return
     */
    private static boolean connectionPossible(final TRSTerm s, final TRSTerm t) {
        final Set<FunctionSymbol> fs = s.getFunctionSymbols();
        if (fs.removeAll(t.getFunctionSymbols())) {
            return true;
        }
        final Set<TRSVariable> vs = s.getVariables();
        return vs.removeAll(t.getVariables());
    }


    private static final Set<Rule> EMPTY_RULE_SET = new HashSet<Rule>(0);


    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter)
        throws AbortionException {


        if (this.subterm) {
            return QDPSizeChangeProcessor.processWithSubterm(qdp, aborter);
        }

        boolean useATrans;
        // currently unsure, whether subterm can be used in combination with A-Transformation
        // is sound. If this is the case, then one should move the
        // aTransformation code before the processWithSubterm
        // TODO: currently atrans is disabled
        /*
        if (qdp.getUsableApplicativeInfo().aTransformable) {
            useATrans = true;
            qdp = qdp.getUsableATransformed();
        } else {
        */
            useATrans = false;
        /*}*/

        final Set<FunctionSymbol> headSyms = qdp.getHeadSymbols();
        final QUsableRules qUsableRules = qdp.getQUsableRulesCalculator();

        // an argument rule for a dp s -> t is either
        // s -> t_i, if t = f(..t_i..) and f is a headsymbol, or s -> t, otherwise

        final Set<Rule> mustRules = new LinkedHashSet<Rule>();  // the set of argument rules resulting in usable
                                                          // rules that must be considered
        final Set<Rule> mayRules   = new LinkedHashSet<Rule>(); // the set of argument rules resulting in usable
                                                          // rules that may be considered
        final Set<Rule> harmlessRules = new LinkedHashSet<Rule>(); // the set of argument rules resulting in no usable rules

        // the above three sets are disjoint

        // now calculate the contents for the three sets
        final Set<Rule> dps = qdp.getP();
        for (final Rule dp : dps) {
            final TRSFunctionApplication s = dp.getLeft();
            if (s.getRootSymbol().getArity() == 0) {
                return ResultFactory.unsuccessful();
            }
            final TRSTerm t = dp.getRight();
            if (t.isVariable()) {
                harmlessRules.add(dp);
            } else {
                final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                final FunctionSymbol f = ft.getRootSymbol();
                final int arity = f.getArity();
                final boolean head = headSyms.contains(f);
                if (arity == 0 && head) {
                    return ResultFactory.unsuccessful();
                } else {
                    if (head) {
                        final Set<Rule> addHere = arity == 1 ? mustRules : mayRules;
                        for (final TRSTerm arg : ft.getArguments()) {
                            if (QDPSizeChangeProcessor.connectionPossible(s, arg)) {
                                final Rule argRule = Rule.create(s, arg);
                                if (qUsableRules.hasUsableRules(argRule)) {
                                    addHere.add(argRule);
                                } else {
                                    harmlessRules.add(argRule);
                                }
                            }
                        }
                    } else {
                        if (QDPSizeChangeProcessor.connectionPossible(s, t)) {
                            if (qUsableRules.hasUsableRules(dp)) {
                                mustRules.add(dp);
                            } else {
                                harmlessRules.add(dp);
                            }
                        }
                    }
                }
            }
        }

        mayRules.removeAll(mustRules);

        // okay, we now have the must, may, and harmless rules

        // check against limits;

        final int nrOfMust = mustRules.size();
        int nrOfAllowedMayRules = this.usableArgumentsRestriction - nrOfMust;
        if (nrOfAllowedMayRules < 0) {
            return ResultFactory.unsuccessful();
        }
        nrOfAllowedMayRules = Math.min(nrOfAllowedMayRules, mayRules.size());


        // okay, now we have to add at most nrOfMayRules many rules
        // from may to the set of usable argument rules

        // we have to consider these argRules
        final Set<Rule> definiteArgRules = harmlessRules;
        definiteArgRules.addAll(mustRules);

        // and hence have to determine a filtering for these symbols
        final Set<FunctionSymbol> definiteSignature = CollectionUtils.getFunctionSymbols(definiteArgRules);
        definiteSignature.removeAll(headSyms);

        // a map from may rules to new elements of the signature
        final Map<Rule, Set<FunctionSymbol>> mayRulesWithSignature = new LinkedHashMap<Rule, Set<FunctionSymbol>>(mayRules.size());
        // and a Set of all possible symbols only occurring in may rules
        final Set<FunctionSymbol> maySignature = new LinkedHashSet<FunctionSymbol>();
        for (final Rule mayRule : mayRules) {
            final Set<FunctionSymbol> signature = mayRule.getFunctionSymbols();
            signature.removeAll(headSyms);
            signature.removeAll(definiteSignature);
            mayRulesWithSignature.put(mayRule, signature);
            maySignature.addAll(signature);
        }

        Set<Rule> usableArgRules; // the set of argument rules that will be considered (= must cup harmless cup subset of may)
        usableArgRules = definiteArgRules;

        Set<FunctionSymbol> usableSignature; // the signature we may use for the AFS in the graphs
        usableSignature = definiteSignature;

        final PowerSet<Rule> possibleMayRuleSets = new PowerSet<Rule>(ImmutableCreator.create(mayRules), nrOfAllowedMayRules, false);

        final RuleChecker ruleChecker = this.factory == null ? new POLORuleChecker(this.range,this.engine) : this.factory.getRuleChecker();


        // iterate over all possible currentMaySets
        // this has to be done in ascending order, otherwise the EMBEdgeConnector should
        // not throw WANT EDGE exceptions in case that a mayRule leads to no edge
        for (final Set<Rule> currentMayRules : possibleMayRuleSets) {
            aborter.checkAbortion();

            usableArgRules.addAll(currentMayRules);

            Map<Rule, QActiveCondition> usableRules = null;
            Map<Rule, QActiveCondition> specializedUsableRules = null;

            //do a fast check, whether in general sct is possible for the current set of usableArgRules
            if (null != QDPSizeChangeProcessor.solveWithSizeChange(qdp, QDPSizeChangeProcessor.getApproximateEdgeConnector(usableArgRules), aborter)) {

                // okay, we may succeed, so let us compute the usable signature
                for (final Rule mayRule : currentMayRules) {
                    usableSignature.addAll(mayRulesWithSignature.get(mayRule));
                }

                // iterate over all AFS over the usableSignature
                for (final Afs afs : Afs.enumerateAfss(usableSignature, true, this.afsRestriction)) {

                    aborter.checkAbortion();
                    final Map<Rule, SizeChangeGraph> sizeChangeSolution = QDPSizeChangeProcessor.solveWithSizeChange(qdp, QDPSizeChangeProcessor.getEMBEdgeConnector(currentMayRules, usableArgRules, afs), aborter);
                    if (sizeChangeSolution != null) {

                        Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>> orderSolution;

                        if (this.usableArgumentsRestriction == 0) {
                            specializedUsableRules = null;
                        } else {
                            if (usableRules == null) {
                                usableRules = qUsableRules.getActiveConditions(usableArgRules, this.mergeMutual);
                            }
                            specializedUsableRules =
                                QUsableRules.getSpecializedActiveConditions(
                                    usableRules, afs);
                        }


                        if (this.usableArgumentsRestriction == 0 || specializedUsableRules.isEmpty()) {

                            // we know that there are no usable rules
                            orderSolution = new Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>>(EMB.theEMB, afs, QDPSizeChangeProcessor.EMPTY_RULE_SET);

                        } else {

                            // okay, let us orient the usable rules;
                            orderSolution = ruleChecker.checkRules(specializedUsableRules, afs, aborter);
                        }

                        if (orderSolution != null) {
                            return ResultFactory.proved(new QDPSizeChangeProof(sizeChangeSolution, orderSolution, usableArgRules, headSyms, useATrans ? qdp : null, qdp));
                        }


                    }


                }

                usableSignature.removeAll(maySignature);

            }

            usableArgRules.removeAll(currentMayRules);

        }

        return ResultFactory.unsuccessful();

    }


    public static interface RuleChecker {
        /**
         * returns a triple of an order over terms, an afs, and the set of really oriented usable rules
         * such that the returned afs is an extension of the input afs and
         * the order after filtering contains the embedding order!
         */
        public Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>> checkRules(Map<Rule, QActiveCondition> usableRules, Afs afs, Abortion aborter) throws AbortionException;
    }


    public static class POLORuleChecker implements RuleChecker {

        private final BigInteger range;
        private final SATCheckerFactory factory;

        public POLORuleChecker(final BigInteger range, final SATCheckerFactory factory) {
            this.range = range;
            this.factory = factory;
        }

        @Override
        public Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>> checkRules(final Map<Rule, QActiveCondition> usableRules, final Afs afs, final Abortion aborter) throws AbortionException {
            // TODO maybe parameterize
            final PoloSatConfigInfo config = new PoloSatConfigInfo();
            final SearchAlgorithm searchAlg = SatSearch.create(this.factory,
                    PlainSPCToCircuitConverter.create(new FullSharingFactory<None>(),
                            java.util.Collections.<String, BigInteger>emptyMap(),
                            this.range, config));
            // end of stuff formerly in constructor leading to bug due to unlabelled formulas

            Interpretation inter = Interpretation.create();
            final Set<VarPolyConstraint> embConstraints = inter.extendForEmb(afs);

            for (final FunctionSymbol f : CollectionUtils.getFunctionSymbols(usableRules.keySet())) {
                inter.extend(f, 1, aborter);
            }

            final Pair<Set<SimplePolyConstraint>, Set<VarPolyConstraint>> constraints = inter.getActiveRuleConstraints(usableRules, null, 1, aborter);
            final POLOSolver poloSolver = POLOSolver.create(inter, searchAlg,
                    SimplificationMode.MAXIMUM, true, false);
            poloSolver.setAllowWeakMonotonicity(true);
            embConstraints.addAll(constraints.y);
            final POLO solution = poloSolver.solve(constraints.x, aborter, embConstraints);
            if (solution == null) {
                return null;
            } else {

                // calculate really oriented rules
                inter = solution.getInterpretation();
                final Set<Rule> orientedRules = new TreeSet<Rule>();
                for (final Map.Entry<Rule, QActiveCondition> usableRule : usableRules.entrySet()) {
                    final SimplePolynomial condition = inter.getActiveConstraint(usableRule.getValue());
                    if (condition.equals(SimplePolynomial.ONE)) {
                        orientedRules.add(usableRule.getKey());
                    } else if (!condition.equals(SimplePolynomial.ZERO)) {
                        if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                            final String message = "Internal error: having active condition not being 0 or 1 after the polo solution: "+condition;
                            System.err.println(message);
                            System.err.println(usableRules);
                            System.err.println(inter);
                            QDPSizeChangeProcessor.log.log(Level.SEVERE, message);
                        }

                        orientedRules.add(usableRule.getKey());
                    }
                }


                if (Globals.useAssertions) {
                    for (final Rule rule : orientedRules) {
                        Constraint<TRSTerm> c;
                        c = Constraint.create(rule.getLeft(), rule.getRight(), OrderRelation.GE);
                        assert solution.solves(c);
                    }
                }

                return new Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>>(solution, null, orientedRules);
            }
        }

    } // end of POLORuleChecker

    public static interface SATSCTEncoder {

        POFormula encode(Map<Rule, QActiveCondition> usableRules, Afs initialAfs, Abortion aborter) throws AbortionException;

        boolean isAllowQuasi();

        Afs getAfs(Set<aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<None>> knownTrue);

        QActiveOrder getOrder(Set<aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<None>> knownTrue, Afs afs);

    }

    public static class SATPORuleChecker implements RuleChecker {

        private final SolverFactory factory;
        private final boolean unary = false;

        public SATPORuleChecker(final SolverFactory factory) {
            this.factory = factory;
        }

        @Override
        public Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>> checkRules(final Map<Rule, QActiveCondition> usableRules, final Afs initialAfs, final Abortion aborter) throws AbortionException {
            /**
             * returns a triple of an order over terms, an afs, and the set of really oriented usable rules
             * such that the returned afs is an extension of the input afs and
             * the order after filtering contains the embedding order!
             */
            long time = System.nanoTime();
            final FormulaFactory<None> formulaFactory = new FullSharingFlatteningFactory<None>();
            final SATSCTEncoder encoder = this.factory.getSATSCTEncoder(formulaFactory);
            if (encoder == null) {
                return null;
            }
            aborter.checkAbortion();
            final POFormula poFormula = encoder.encode(usableRules, initialAfs, aborter);
            time = System.nanoTime()-time;
            long total = time;
            long encodeTime = time;
            QDPSizeChangeProcessor.log.log(Level.FINER, "Encoding to partial order constraints: {0} ms\n", time/1000000);

            time = System.nanoTime();
            aborter.checkAbortion();
            PLEncoder plEncoder;
            if (!this.unary) {
                plEncoder = new SimpleBinaryPLEncoder(formulaFactory, encoder.isAllowQuasi());
            } else {
                plEncoder = new SimpleUnaryPLEncoder(formulaFactory, encoder.isAllowQuasi());
            }
            final Formula<None> formula = plEncoder.toPropositionalFormula(poFormula, aborter);
            time = System.nanoTime()-time;
            total += time;
            encodeTime += time;
            QDPSizeChangeProcessor.log.log(Level.FINER, "Encoding to propositional logic: {0} ms\n", time/1000000);

            time = System.nanoTime();
            int res[];
            aborter.checkAbortion();
            final SATChecker satChecker = this.factory.getSATCheckerFactory().getSATChecker();
            try {
                res = satChecker.solve(formula, aborter);
            } catch (final SolverException e) {
                return null;
            }
            time = System.nanoTime()-time;
            total += time;
            QDPSizeChangeProcessor.log.log(Level.FINER, "SAT solving: {0} ms\n", time/1000000);
            if (res != null) {

                time = System.nanoTime();
                final Set<aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<None>> knownTrue = poFormula.decode(res, formula.getId());
                final Afs afs = encoder.getAfs(knownTrue);
                if (Globals.useAssertions) {
                    for (final Triple<FunctionSymbol, YNM[], Boolean> filter : initialAfs.getFilterings()) {
                        final Pair<YNM[], Boolean> other = afs.getFiltering(filter.x);
                        assert(filter.y.length == other.x.length);
                        assert(filter.z.equals(other.y));
                        for (int i = 0; i < filter.y.length; i++) {
                            assert(filter.y[i].equals(other.x[i]));
                        }
                    }
                }
                final QActiveOrder order = encoder.getOrder(knownTrue, afs);
                time = System.nanoTime()-time;
                total += time;
                QDPSizeChangeProcessor.log.log(Level.FINER, "Decoding Afs and LPO: {0} ms\n", time/1000000);

                final Set<Rule> usedRules = new LinkedHashSet<Rule>();
                for (final Map.Entry<Rule, QActiveCondition> ruleCond : usableRules.entrySet()) {
                    final Rule rule = ruleCond.getKey();
                    final QActiveCondition cond = ruleCond.getValue();
                    if (cond.specialize(afs) == QActiveCondition.TRUE) {
                        usedRules.add(rule);
                    }
                }
                return new Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>>(order,afs,usedRules);
            }
            QDPSizeChangeProcessor.log.log(Level.FINE, "Total time: {0} ms\n", total/1000000);
            return null;
        }

    }

    @SuppressWarnings("serial")
    private static class EdgeShouldBeUsedException extends Exception {}
    private static final EdgeShouldBeUsedException WANT_EDGE = new EdgeShouldBeUsedException();

    private static interface EdgeConnector {
        /**
         * checks whether there is a connection from each leftArg to rightArg under
         * the assumption that the rule used was left->right and left = f(leftArgs), right|_q = rightArg
         */
        public Map<Integer, Boolean> connect(TRSFunctionApplication left, List<? extends TRSTerm> leftArgs, TRSTerm rightArg) throws EdgeShouldBeUsedException;
        // null = no edge, False = equal edge, True = strict edge from each position to the rightArg
        // if there is no edge then the null map must be returned


        /**
         * checks whether there is a connection from each left to rightArg under
         * the assumption that the rule used was left->right and right|_q = rightArg
         */
        public Map<Integer, Boolean> connect(TRSFunctionApplication left, TRSTerm rightArg) throws EdgeShouldBeUsedException;
        // null = no edge, ZERO_FALSE_MAP = equal edge, ZERO_TRUE_MAP = strict edge from each position to the rightArg
    }

    private static final Map<Integer, Boolean> ZERO_TRUE_MAP;
    private static final Map<Integer, Boolean> ZERO_FALSE_MAP;
    static {
        ZERO_TRUE_MAP = new LinkedHashMap<Integer, Boolean>(1);
        ZERO_FALSE_MAP = new LinkedHashMap<Integer, Boolean>(1);
        QDPSizeChangeProcessor.ZERO_TRUE_MAP.put(0, true);
        QDPSizeChangeProcessor.ZERO_FALSE_MAP.put(0, false);
    }


    private static EdgeConnector getApproximateEdgeConnector(final Set<Rule> availableArgRules) {
        return new EdgeConnector() {
            private Map<Integer, Boolean> unusedMap = null;
            @Override
            public Map<Integer, Boolean> connect(final TRSFunctionApplication left, final List<? extends TRSTerm> leftArgs, final TRSTerm rightArg) {
                if (availableArgRules.contains(Rule.create(left, rightArg))) {
                    Map<Integer, Boolean> map = this.unusedMap;
                    if (map == null) {
                        map = new LinkedHashMap<Integer, Boolean>(6);
                    } else {
                        this.unusedMap = null;
                    }
                    int i = 0;
                    for (final TRSTerm leftArg : leftArgs) {
                        if (leftArg.equals(rightArg)) {
                            map.put(i, Boolean.FALSE);
                        } else if (QDPSizeChangeProcessor.connectionPossible(leftArg, rightArg)) {
                            map.put(i, Boolean.TRUE);
                        }
                        i++;
                    }
                    if (map.isEmpty()) {
                        this.unusedMap = map;
                        return null;
                    } else {
                        return map;
                    }
                } else {
                    return null;
                }
            }
            @Override
            public Map<Integer, Boolean> connect(final TRSFunctionApplication left, final TRSTerm rightArg) {
                if (availableArgRules.contains(Rule.create(left, rightArg))) {
                    if (left.equals(rightArg)) {
                        return QDPSizeChangeProcessor.ZERO_FALSE_MAP;
                    } else if (QDPSizeChangeProcessor.connectionPossible(left, rightArg)) {
                        return QDPSizeChangeProcessor.ZERO_TRUE_MAP;
                    } else {
                        return null;
                    }
                } else {
                    return null;
                }
            }
        };
    };

    private static EdgeConnector getEMBEdgeConnector(final Set<Rule> mayRules, final Set<Rule> allUsableRules, final Afs afs) {
        return new EdgeConnector() {
            private Map<Integer, Boolean> unusedMap = null;
            @Override
            public Map<Integer, Boolean> connect(final TRSFunctionApplication left, final List<? extends TRSTerm> leftArgs, final TRSTerm rightArg) throws EdgeShouldBeUsedException {
                final Rule argRule = Rule.create(left, rightArg);
                if (allUsableRules.contains(argRule)) {
                    Map<Integer, Boolean> map = this.unusedMap;
                    if (map == null) {
                        map = new LinkedHashMap<Integer, Boolean>(6);
                    } else {
                        this.unusedMap = null;
                    }
                    int i = 0;
                    final TRSTerm rightFilter = afs.filterTerm(rightArg);
                    for (final TRSTerm leftArg : leftArgs) {
                        final TRSTerm leftFilter = afs.filterTerm(leftArg);
                        if (leftFilter.equals(rightFilter)) {
                            map.put(i, Boolean.FALSE);
                        } else if (EMB.theEMB.inRelation(leftFilter, rightFilter)) {
                            map.put(i, Boolean.TRUE);
                        }
                        i++;
                    }
                    if (map.isEmpty()) {
                        if (mayRules.contains(argRule)) {
                            // waaah, we should have used at least one edge
                            // to the rightArg, because otherwise
                            // we can have done it also with a smaller may-Rule set
                            // which was not the case
                            throw QDPSizeChangeProcessor.WANT_EDGE;
                        } else {
                            this.unusedMap = map;
                            return null;
                        }
                    } else {
                        return map;
                    }
                } else {
                    return null;
                }
            }
            @Override
            public Map<Integer, Boolean> connect(final TRSFunctionApplication left, final TRSTerm rightArg) throws EdgeShouldBeUsedException {
                final Rule argRule = Rule.create(left, rightArg);
                if (allUsableRules.contains(argRule)) {
                    final TRSTerm leftFilter = afs.filterTerm(left);
                    final TRSTerm rightFilter = afs.filterTerm(rightArg);
                    if (leftFilter.equals(rightFilter)) {
                        return QDPSizeChangeProcessor.ZERO_FALSE_MAP;
                    } else if (EMB.theEMB.inRelation(leftFilter, rightFilter)) {
                        return QDPSizeChangeProcessor.ZERO_TRUE_MAP;
                    } else {
                        if (mayRules.contains(argRule)) {
                            throw QDPSizeChangeProcessor.WANT_EDGE;
                        } else {
                            return null;
                        }
                    }
                } else {
                    return null;
                }
            }
        };
    }

    private static EdgeConnector getSubtermConnector() {
        // create new connectors, as otherwise race conditions on the unusedMap may arise
        return
            new EdgeConnector() {

                private Map<Integer, Boolean> unusedMap = null;

                @Override
                public Map<Integer, Boolean> connect(
                    final TRSFunctionApplication left,
                    final List<? extends TRSTerm> leftArgs,
                    final TRSTerm rightArg
                ) {
                    Map<Integer, Boolean> map = this.unusedMap;
                    if (map == null) {
                        map = new LinkedHashMap<Integer, Boolean>(6);
                    } else {
                        this.unusedMap = null;
                    }
                    int i = 0;
                    for (final TRSTerm leftArg : leftArgs) {
                        if (leftArg.equals(rightArg)) {
                            map.put(i, Boolean.FALSE);
                        } else if (leftArg.hasProperSubterm(rightArg)) {
                            map.put(i, Boolean.TRUE);
                        }
                        i++;
                    }
                    if (map.isEmpty()) {
                        this.unusedMap = map;
                        return null;
                    } else {
                        return map;
                    }
                }

                @Override
                public Map<Integer, Boolean> connect(final TRSFunctionApplication left, final TRSTerm rightArg) {
                    if (left.equals(rightArg)) {
                        return QDPSizeChangeProcessor.ZERO_FALSE_MAP;
                    } else if (left.hasProperSubterm(rightArg)) {
                        return QDPSizeChangeProcessor.ZERO_TRUE_MAP;
                    } else {
                        return null;
                    }
                }

            };
    }

    private static Result processWithSubterm(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        QDPSizeChangeProcessor.log.log(Level.CONFIG, "Using Size-Change with subterm criterion.\n");
        final Map<Rule, SizeChangeGraph> graphsForProof = QDPSizeChangeProcessor.solveWithSizeChange(qdp, QDPSizeChangeProcessor.getSubtermConnector(), aborter);

        if (graphsForProof == null) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(new QDPSizeChangeProof(graphsForProof, null, null, null, null, qdp));
        }
    }

    /**
     * solves a qdp problem with the size-change criterion.
     * How to build the graphs will be determined by the connector
     * @param qdp
     * @param connector
     * @param aborter
     * @return null, if we do not have size-change termination, the map of dps to their size-change graphs, otherwise
     * @throws AbortionException
     */
    private static Map<Rule, SizeChangeGraph> solveWithSizeChange(final QDPProblem qdp, final EdgeConnector connector, final Abortion aborter) throws AbortionException {
        final ImmutableSet<FunctionSymbol> headSyms = qdp.getHeadSymbols();
        final Graph<Rule,?> dGraph = qdp.getDependencyGraph().getGraph();
        final ImmutableSet<Set<Node<Rule>>> equivClasses = dGraph.getEquivalenceClasses();
        final Set<SizeChangeGraph> initialSCGs = new LinkedHashSet<SizeChangeGraph>();
        final Map<Rule, SizeChangeGraph> graphsForProof = new LinkedHashMap<Rule, SizeChangeGraph>();

        // build initial SCGs
        try {
            for (final Set<Node<Rule>> eqClass : equivClasses) {
                aborter.checkAbortion();
                final Node<Rule> representative = eqClass.iterator().next();
                for (final Node<Rule> dp : eqClass) {
                    final SizeChangeGraph scg = SizeChangeGraph.create(dp.getObject(), representative, headSyms, connector);
                    if (scg.isCritical(dGraph)) {
                        return null;
                    } else {
                        initialSCGs.add(scg);
                        graphsForProof.put(dp.getObject(), scg);
                    }
                }
            }
        } catch (final EdgeShouldBeUsedException e) {
            return null;
        }

        // and perform closure
        if (QDPSizeChangeProcessor.noCriticalGraphInSizeChangeClosure(initialSCGs, dGraph, aborter)) {
            return graphsForProof;
        } else {
            return null;
        }
    }



    /**
     * takes an initial set of Size-Change graphs (which have to be non-critical)
     * and the underlying Dependency Graph
     * @param initialGraphs
     * @param dGraph
     * @return
     */
    private static boolean noCriticalGraphInSizeChangeClosure(
            final Set<SizeChangeGraph> initialGraphs,
            final Graph<Rule, ?> dGraph,
            final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            for (final SizeChangeGraph scg : initialGraphs) {
                assert(!scg.isCritical(dGraph));
            }
        }
        Set<SizeChangeGraph> todo = new LinkedHashSet<SizeChangeGraph>(initialGraphs); // connect with initial graphs
        final Set<SizeChangeGraph> done = new LinkedHashSet<SizeChangeGraph>(initialGraphs); // graphs already seen
        int count = 0;
        while (!todo.isEmpty()) {
            if (count == 100) {
                count = 0;
                aborter.checkAbortion();
            } else {
                count++;
            }
            final Set<SizeChangeGraph> newGraphs = new LinkedHashSet<SizeChangeGraph>();
            for (final SizeChangeGraph base : initialGraphs) {
                for (final SizeChangeGraph scg : todo) {
                    final SizeChangeGraph newGraph = scg.connect(base, dGraph);
                    if (newGraph != null) {
                        if (done.add(newGraph)) {
                            if (newGraph.isCritical(dGraph)) {
                                return false;
                            } else {
                                newGraphs.add(newGraph);
                            }
                        }
                    }
                }
            }
            todo = newGraphs;
        }
        return true;
    }



    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        if (!(qdp.getMinimal() || qdp.QsupersetOfLhsR())) {
            return false;
        }

//      TODO: graph connections should be such that there is no s -> x, F( ) -> .. connected, etc.
        if (Globals.DEBUG_THIEMANN) {
            System.err.println("graph connections should be such that there is no s -> x, F( ) -> .. connected for Size-change");
        }

        // currently perform harder check that only pairs F(.) -> G(.) occur.
        final Set<FunctionSymbol> headSyms = qdp.getHeadSymbols();
        for (final Rule rule : qdp.getP()) {
            if (headSyms.contains(rule.getLeft().getRootSymbol())) {
                final TRSTerm right = rule.getRight();
                if (!right.isVariable() && headSyms.contains(((TRSFunctionApplication)right).getRootSymbol())) {
                    continue;
                }
            }
            return false;
        }
        return true;
    }

    private static final class SizeChangeGraph {

        private final Node<Rule> from;
        private final Node<Rule> to;
        private final Map<Integer, Boolean>[] edgeMap; // null, if there are no edges
        // otherwise for each position on the right there is a map in the array:
        // if there are no edges to this position the map is null
        // and otherwise we have a mapping from positions of the lhs to the corresponding
        // label (True = Strict, False = non-strict)
        private final int hashcode;


        /**
         * creates a new SCG for the given DP and its equivalent class
         * in the DP-graph using the subterm criterion.
         * Returns null if we encounter an arity of 0 (headsym with arity 0)
         * or a graph without edges
         * @param s_to_t
         * @param equivClass
         * @param headSyms
         * @return
         * @throws EdgeShouldBeUsedException
         */
        @SuppressWarnings("unchecked")
        public static SizeChangeGraph create(final Rule s_to_t, final Node<Rule> equivClass, final Set<FunctionSymbol> headSyms, final EdgeConnector connector) throws EdgeShouldBeUsedException {
            final TRSFunctionApplication s = s_to_t.getLeft();
            final TRSTerm t = s_to_t.getRight();
            final boolean leftHead = headSyms.contains(s.getRootSymbol());
            boolean rightHead;
            int rightArity;
            if (t.isVariable()) {
                rightHead = false;
                rightArity = 1;
            } else {
                final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                final FunctionSymbol f = ft.getRootSymbol();
                rightHead = headSyms.contains(f);
                rightArity = rightHead ? f.getArity() : 1;
            }
            Map<Integer, Boolean>[] allEdges = new Map[rightArity];

            boolean gotEdge = false;

            if (leftHead && rightHead) {
                final List<? extends TRSTerm> sArgs = s.getArguments();
                int i=0;
                for (final TRSTerm tArg : ((TRSFunctionApplication) t).getArguments()) {
                    final Map<Integer, Boolean> iEdges = connector.connect(s, sArgs, tArg);
                    allEdges[i] = iEdges;
                    if (iEdges != null) {
                        gotEdge = true;
                    }
                    i++;
                }
            } else if (leftHead) {
                // but not right head
                final Map<Integer, Boolean> edges = connector.connect(s, s.getArguments(), t);
                if (edges != null) {
                    allEdges[0] = edges;
                    gotEdge = true;
                }
            } else if (rightHead) {
                // and no left head
                int i=0;
                for (final TRSTerm tArg : ((TRSFunctionApplication) t).getArguments()) {
                    final Map<Integer, Boolean> iEdges = connector.connect(s, tArg);
                    allEdges[i] = iEdges;
                    if (iEdges != null) {
                        gotEdge = true;
                    }
                    i++;
                }
            } else {
                // no left and no right head
                final Map<Integer, Boolean> edges = connector.connect(s, t);
                if (edges != null) {
                    allEdges[0] = edges;
                    gotEdge = true;
                }
            }
            if (!gotEdge) {
                allEdges = null;
            }
            return new SizeChangeGraph(equivClass, equivClass, allEdges);
        }

        private SizeChangeGraph(final Node<Rule> from, final Node<Rule> to, final Map<Integer, Boolean>[] edgeMap) {
            this.from = from;
            this.to = to;
            this.edgeMap = edgeMap;
            int hashCode = from.hashCode()*0xfa43ba53+to.hashCode()*0x1893cbaf;
            if (edgeMap != null) {
                final int n = edgeMap.length;
                for (int i=0; i<n; i++) {
                    hashCode = hashCode * 0x4930fbaf + (edgeMap[i] == null ? 0x73382403 : 0x24849021*edgeMap[i].hashCode());
                }
            }
            this.hashcode = hashCode;
        }

        /**
         * checks whether the graph is critical,
         * i.e. it contains no edges or it is idempotent
         * and does not contain an edge of the form x > x
         * @param dpGraph
         * @return
         */
        public boolean isCritical(final Graph<Rule, ?> dpGraph) {
            if (this.edgeMap == null) {
                // a graph without edges is critical
                return true;
            }
            if (dpGraph.contains(this.to, this.from) && this.equals(this.connect(this, dpGraph))) {
                // idempotent
                // check for edge x > x
                final int n = this.edgeMap.length;
                for (int i=0; i<n; i++) {
                    final Map<Integer, Boolean> edges = this.edgeMap[i];
                    if (edges != null) {
                        final Boolean b = edges.get(i);
                        if (b != null && b) {
                            return false;
                        }
                    }
                }
                return true;
            } else {
                //  not idempotent
                return false;
            }
        }

        @SuppressWarnings("unchecked")
        public SizeChangeGraph connect(final SizeChangeGraph other, final Graph<Rule, ?> dpGraph) {
            if (dpGraph.contains(this.to, other.from)) {
                Map<Integer, Boolean>[] edgeMap;
                if (this.edgeMap == null || other.edgeMap == null) {
                    edgeMap = null;
                } else {
                    Map<Integer, Boolean> spareMap = null;
                    boolean gotEdge = false;
                    final int n = other.edgeMap.length;
                    edgeMap = new Map[n];
                    for (int i = 0; i<n; i++) {
                        final Map<Integer, Boolean> edges = other.edgeMap[i];
                        if (edges != null) {
                            Map<Integer, Boolean> newEdges;
                            if (spareMap == null) {
                                newEdges = new LinkedHashMap<Integer, Boolean>(6);
                            } else {
                                newEdges = spareMap;
                                spareMap = null;
                            }
                            for (final Map.Entry<Integer, Boolean> edge : edges.entrySet()) {
                                final int j = edge.getKey();
                                final boolean greater = edge.getValue();
                                final Map<Integer, Boolean> thisEdges = this.edgeMap[j];
                                if (thisEdges != null) {
                                    for (final Map.Entry<Integer, Boolean> thisEdge : thisEdges.entrySet()) {
                                        final boolean gr = greater || thisEdge.getValue();
                                        final Integer k = thisEdge.getKey();
                                        if (gr) {
                                            newEdges.put(k, Boolean.TRUE);
                                        } else {
                                            final Boolean old = newEdges.put(k, Boolean.FALSE);
                                            if (old != null && old.booleanValue()) {
                                                newEdges.put(k, old);
                                            }
                                        }
                                    }
                                }
                            }
                            if (newEdges.isEmpty()) {
                                edgeMap[i] = null;
                                spareMap = newEdges;
                            } else {
                                edgeMap[i] = newEdges;
                                gotEdge = true;
                            }
                        } else {
                            edgeMap[i] = null;
                        }
                    }

                    if (!gotEdge) {
                        edgeMap = null;
                    }
                }

                return new SizeChangeGraph(this.from, other.to, edgeMap);
            } else {
                return null;
            }
        }

        @Override
        public boolean equals(final Object other) {
            final SizeChangeGraph scg = (SizeChangeGraph) other;
            if (scg.hashcode == this.hashcode &&
                scg.from == this.from &&
                scg.to == this.to) {
                final Map<Integer,Boolean>[] thisMap = this.edgeMap;
                final Map<Integer,Boolean>[] scgMap  = scg.edgeMap;
                if (thisMap == null) {
                    return scgMap == null;
                }
                if (scgMap == null) {
                    return false;
                }
                final int n = thisMap.length;
                for (int i=0; i<n; i++) {
                    final Map<Integer,Boolean> thisM = thisMap[i];
                    if (thisM == null) {
                        if (scgMap[i] != null) {
                            return false;
                        }
                    } else {
                        if (thisM.equals(scgMap[i])) {
                        } else {
                            return false;
                        }
                    }
                }
                return true;
            } else {
                return false;
            }

        }

        @Override
        public int hashCode() {
            return this.hashcode;
        }

        @Override
        public String toString() {
            String res = this.from.getObject() + " ... " + this.to.getObject() + ": ";
            boolean first = true;
            if (this.edgeMap != null) {
                int i = 0;
                for (final Map<Integer, Boolean> edges : this.edgeMap) {
                    i++;
                    if (edges != null) {
                        for (final Map.Entry<Integer, Boolean> edge : edges.entrySet()) {
                            if (first) {
                                first = false;
                            } else {
                                res += ", ";
                            }
                            res += (edge.getKey().intValue()+1) + (edge.getValue() ? " > " : " >= ") + i;
                        }
                    }
                }
                if (Globals.useAssertions) {
                    assert(!first);
                }
            } else {
                res += "no edges";
            }
            return res;
        }

    }


    private static final class QDPSizeChangeProof extends QDPProof {

        private final Map<Rule,SizeChangeGraph> graphs;
        private final Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>> orderSolution;
        private final Set<Rule> usableArgRules;
        private final Set<FunctionSymbol> headSyms;
        private final QDPProblem aTransQDP; // null if not aTransformed
        private final BasicObligation origObl;

        private QDPSizeChangeProof (final Map<Rule,SizeChangeGraph> graphs, final Triple<ExportableOrder<TRSTerm>, Afs, Set<Rule>> orderSolution, final Set<Rule> usableArgRules, final Set<FunctionSymbol> headSyms, final QDPProblem aTransQDP, final BasicObligation origObl) {
            this.graphs = graphs;
            this.orderSolution = orderSolution;
            this.usableArgRules = usableArgRules;
            this.headSyms = headSyms;
            this.aTransQDP = aTransQDP;
            this.origObl = origObl;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {

            StringBuilder result;
            result = new StringBuilder();
            if (this.orderSolution == null) {
                result.append("By using the subterm criterion "+o.cite(Citation.SUBTERM_CRITERION)+ " together with the size-change analysis "+o.cite(Citation.AAECC05)+" we have proven that there" +
                " are no infinite chains for this DP problem. ");
            } else {
                if (this.aTransQDP != null) {
                    result.append("We first transformed the problem by the A-transformation "+o.cite(Citation.FROCOS05)+" the following DP-problem."+o.cond_linebreak());
                    result.append(this.aTransQDP.export(o));
                }
                final Afs afs = this.orderSolution.y;
                result.append("We used the following order "+(afs == null ? "" : "and afs ")+ "together with the size-change analysis "+o.cite(Citation.AAECC05)+" to show that there" +
                " are no infinite chains for this DP problem. "+o.paragraph());
                result.append(o.export("Order:")+o.export(this.orderSolution.x)+o.paragraph());
                if (afs != null) {
                    result.append("AFS: "+o.linebreak()+afs.export(o)+o.paragraph());
                }
            }
            result.append(o.paragraph());
            result.append("From the DPs we obtained the following set of size-change graphs:\n");
            final ArrayList<Object> scgs = new ArrayList<Object>(this.graphs.size());
            for (final Map.Entry<Rule,SizeChangeGraph> scg : this.graphs.entrySet()) {
                final Rule dp = scg.getKey();
                final TRSFunctionApplication s = dp.getLeft();
                final TRSTerm t = dp.getRight();
                final StringBuilder res = new StringBuilder();
                res.append(o.export(dp));
                if (this.orderSolution != null) {
                    res.append(" (allowed arguments on rhs = ");

                    List<Integer> allowedArgs;
                    if (t.isVariable()) {
                        allowedArgs = null;
                    } else {
                        final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                        if (this.headSyms.contains(ft.getRootSymbol())) {
                            allowedArgs = new LinkedList<Integer>();
                            int i = 0;
                            for (final TRSTerm ti : ft.getArguments()) {
                                i++;
                                if (this.usableArgRules.contains(Rule.create(s,ti))) {
                                    allowedArgs.add(Integer.valueOf(i));
                                }
                            }
                        } else {
                            allowedArgs = null;
                        }
                    }

                    if (allowedArgs == null) {
                        if (this.usableArgRules.contains(dp)) {
                            res.append("epsilon");
                        }
                    } else {
                        res.append(o.set(allowedArgs, Export_Util.SIMPLESET));
                    }

                    res.append(')');
                }

                res.append(o.linebreak()).append("The graph contains the following edges ");

                boolean first = true;
                int i = 0;
                for (final Map<Integer, Boolean> edges : scg.getValue().edgeMap) {
                    i++;
                    if (edges == null) {
                        continue;
                    }
                    for (final Map.Entry<Integer, Boolean> edge : edges.entrySet()) {
                        if (first) {
                            first = false;
                        } else {
                            res.append(", ");
                        }
                        res.append(edge.getKey().intValue()+1).append(edge.getValue() ? " > " : " >= ").append(i);
                    }
                }
                res.append(o.paragraph());
                scgs.add(o.wrapAsRaw(res));
            }

            result.append(o.set(scgs, Export_Util.ITEMIZE));

            if (this.orderSolution != null) {
                result.append(o.paragraph());
                result.append("We oriented the following set of usable rules "+o.cite(new Citation[]{Citation.AAECC05, Citation.FROCOS05})+".\n");
                result.append(o.set(this.orderSolution.z, Export_Util.RULES));
            }
            return result.toString();
        }


        private ExportableOrder<TRSTerm> getOrderForCPF() {
            if (this.orderSolution == null) {
                return null;
            }
            if (this.orderSolution.x instanceof EMB) {
                return new AfsOrder(this.orderSolution.y, EMB.theEMB);
            } else {
                return this.orderSolution.x;
            }
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            final Element scp = CPFTag.SIZE_CHANGE_PROC.createElement(doc);

            if (this.orderSolution == null) {
                final Element sc = CPFTag.SUBTERM_CRITERION.createElement(doc);
                scp.appendChild(sc);
            } else {

                final Element reductionPair = CPFTag.REDUCTION_PAIR.create(doc, this.getOrderForCPF().toCPF(doc, xmlMetaData));
                reductionPair.appendChild(CPFTag.USABLE_RULES.create(doc,
                        CPFTag.rules(doc, xmlMetaData, this.orderSolution.z)));
                scp.appendChild(reductionPair);
            }

            for (final Map.Entry<Rule, SizeChangeGraph> graph : this.graphs.entrySet()) {
                final Element scg = CPFTag.SIZE_CHANGE_GRAPH.createElement(doc);
                scg.appendChild(graph.getKey().toCPF(doc, xmlMetaData));
                int i = 0;
                for (final Map<Integer, Boolean> edges : graph.getValue().edgeMap) {
                    i++;
                    if (edges != null) {
                        for (final Map.Entry<Integer, Boolean> edge : edges.entrySet()) {
                            final Element e = CPFTag.EDGE.createElement(doc);
                            final Element from = CPFTag.POSITION.createElement(doc);
                            from.appendChild(doc.createTextNode("" + (edge.getKey().intValue() + 1)));
                            final Element strict = CPFTag.STRICT.createElement(doc);
                            if (edge.getValue()) {
                                strict.appendChild(doc.createTextNode("true"));
                            } else {
                                strict.appendChild(doc.createTextNode("false"));
                            }
                            final Element to = CPFTag.POSITION.createElement(doc);
                            to.appendChild(doc.createTextNode("" + i));
                            e.appendChild(from);
                            e.appendChild(strict);
                            e.appendChild(to);
                            scg.appendChild(e);
                        }
                    }
                }
                scp.appendChild(scg);
            }

            return CPFTag.DP_PROOF.create(doc, scp);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            ExportableOrder<TRSTerm> order = this.getOrderForCPF();
            return (order == null || order.isCPFSupported() == null) && this.aTransQDP == null;
        }

        @Override
        public String getNonCPFExportableReason(CPFModus modus) {
            return super.getNonCPFExportableReason(modus) + (this.aTransQDP != null ? " + A-transformation" :
                " with " + this.getOrderForCPF().isCPFSupported());
        }


    }



    public int parseAfsRestriction(final int afsRestriction) {
        return afsRestriction == -1 ? Integer.MAX_VALUE : afsRestriction;
    }

    public int parseUsableArgumentsRestriction(final int usableArgumentsRestriction) {
        return usableArgumentsRestriction == -1 ? Integer.MAX_VALUE : usableArgumentsRestriction;
    }

    public static class Arguments {
        public boolean subterm = false;
        public SolverFactory order;
        public int afsRestriction = 2;
        public boolean mergeMutual = false;
        public int usableArgumentsRestriction = 0;
        public int Range = 1;
        public Engine engine;
    }
}
