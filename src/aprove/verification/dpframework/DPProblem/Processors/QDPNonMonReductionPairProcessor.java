package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.QActiveCondition.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Similar to QDPReductionPairProcessor, but here we use non-monotonic
 * reduction pairs.
 *
 * Here, we use a max-min-polynomial order over the naturals with negative
 * constants and negative coefficients of variables to compare terms.
 * Hence, we need to orient the general usable rules (weakly).
 *
 * @author Carsten Fuhs
 * @see QDPReductionPairProcessor
 */
public class QDPNonMonReductionPairProcessor extends QDPProblemProcessor {

    private final NonMonPOLOFactory factory;
    private final boolean allstrict;

    @ParamsViaArgumentObject
    public QDPNonMonReductionPairProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;

        final NonMonPOLOFactory.Arguments facArgs =
            new NonMonPOLOFactory.Arguments();
        facArgs.engine = arguments.engine;
        facArgs.heuristic = arguments.heuristic;
        facArgs.negRange = -Math.abs(arguments.negRange);
        facArgs.posRange = Math.abs(arguments.posRange);
        facArgs.satConverter = arguments.satConverter;
        this.factory = new NonMonPOLOFactory(facArgs);
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        return qdp.getMinimal();
    }

    @Override
    protected Result processQDPProblem(final QDPProblem origqdp, final Abortion aborter) throws AbortionException {
        final QDPNonMonPoloSolver solver = this.factory.getQDPNonMonPoloSolver();

        final Set<Rule> P = origqdp.getP();

        boolean allstrict = this.allstrict;
        if (!allstrict && P.size() == 1) {
            allstrict = true;
        }

        aborter.checkAbortion();
        final NonMonPOLO solvingOrder = solver.solve(origqdp, allstrict, aborter);
        if (solvingOrder != null) {
            return QDPNonMonReductionPairProcessor.getResult(solvingOrder, origqdp);
        }
        return ResultFactory.unsuccessful();
    }


    /**
     * Standard method to compute the result of this processor.
     * @param order
     * @param origqdp
     * @return
     */
    public static Result getResult(
            final NonMonPOLO order,
            final QDPProblem origqdp) throws AbortionException {
        // check which elements of P have been oriented strictly
        Set<Rule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        for (final Rule rule : origqdp.getP()) {
            // only add non-strictly oriented rules
            // actually, using standard representations is not required at this point
            final Constraint<TRSTerm> c = Constraint.create(rule.getLhsInStandardRepresentation(),
                    rule.getRhsInStandardRepresentation(),
                    OrderRelation.GR);
            if (!order.solves(c)) {
                newPRules.add(rule);
            } else {
                deletedPRules.add(rule);
            }
        }

        // Usable Rules are a bit fancier now ;-)
        final ExtendedAfs eafs = order.getExtendedAfs();
        final Map<Rule, Direction> generalUsableRules = QDPNonMonReductionPairProcessor.getUsableRules(origqdp, eafs);

        if (Globals.useAssertions) {
            usableLoop: for (final Entry<Rule, Direction> ruleToDir : generalUsableRules.entrySet()) {
                Constraint<TRSTerm> c;
                final Rule rule = ruleToDir.getKey();
                switch (ruleToDir.getValue()) {
                case None:
                    // nothing required :)
                    continue usableLoop;
                case Normal:
                    c = Constraint.create(rule.getLhsInStandardRepresentation(),
                            rule.getRhsInStandardRepresentation(),
                            OrderRelation.GE);
                    break;
                case Reversed:
                    c = Constraint.create(rule.getRhsInStandardRepresentation(),
                            rule.getLhsInStandardRepresentation(),
                            OrderRelation.GE);
                    break;
                case Both:
                    c = Constraint.create(rule.getLhsInStandardRepresentation(),
                            rule.getRhsInStandardRepresentation(),
                            OrderRelation.EQ);
                    break;
                default:
                    throw new RuntimeException("Unknown Dependence "
                            + ruleToDir.getValue());
                }
                assert order.solves(c);
            }

            for (final Rule rule : origqdp.getP()) {
                final Constraint<TRSTerm> c = Constraint.create(rule.getLhsInStandardRepresentation(),
                        rule.getRhsInStandardRepresentation(),
                        OrderRelation.GE);
                assert order.solves(c);
            }
            assert ! deletedPRules.isEmpty();
            for (final Rule rule : deletedPRules) {
                final Constraint<TRSTerm> c = Constraint.create(rule.getLhsInStandardRepresentation(),
                        rule.getRhsInStandardRepresentation(),
                        OrderRelation.GR);
                assert order.solves(c);
            }
        }

        // build smaller subproblem and proof
        final QDPProblem newQdp = origqdp.getSubProblem(ImmutableCreator.create(newPRules));
        final Proof proof = new NonMonReductionPairProof(order, deletedPRules, newPRules, generalUsableRules, origqdp, newQdp);
        return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);
    }

    /**
     * Gets the general usable rules of the qdp given eafs.
     *
     * @param qdp
     * @param eafs
     * @return the general usable rules of this as a map of the rules of R
     *  to the directiuon in which they must be oriented
     */
    private static Map<Rule, Direction> getUsableRules(final QDPProblem qdp, final ExtendedAfs eafs) {
        final Set<Rule> p = qdp.getP();
        final Set<Rule> r = qdp.getR();

        // 1) get defined symbols and their rules
        final QTRSProblem qtrs = qdp.getRwithQ();
        final Set<FunctionSymbol> defSymbols = qtrs.getDefinedSymbolsOfR();
        final Map<FunctionSymbol, ImmutableSet<Rule>> ruleMap = qtrs.getRuleMap();

        // 2) compute set [(called symbol, dependence of called symbol on rhs)]
        // resulting from the rhss of P
        final Set<Pair<FunctionSymbol, Dependence>> pUsableSyms = QDPNonMonReductionPairProcessor.computeDependencesForRules(p, defSymbols, eafs);

        // 3) compute map
        // [defined symbol -> [(called symbol, dependence of called symbol on rhs)]],
        Map<FunctionSymbol, Set<Pair<FunctionSymbol, Dependence>>> fToRhss;
        fToRhss = new LinkedHashMap<FunctionSymbol, Set<Pair<FunctionSymbol, Dependence>>>(ruleMap.size());

        // ... initializing maps with dependences in the process ...,
        Map<FunctionSymbol, Boolean> fCalledIncr, fCalledDecr;
        fCalledIncr = new LinkedHashMap<FunctionSymbol, Boolean>(ruleMap.size());
        fCalledDecr = new LinkedHashMap<FunctionSymbol, Boolean>(ruleMap.size());

        // now compute & init (as announced)
        for (final Entry<FunctionSymbol, ImmutableSet<Rule>> fToItsRules : ruleMap.entrySet()) {
            final FunctionSymbol f = fToItsRules.getKey();
            final Set<Rule> fRules = fToItsRules.getValue();
            final Set<Pair<FunctionSymbol, Dependence>> fUsableSyms = QDPNonMonReductionPairProcessor.computeDependencesForRules(fRules, defSymbols, eafs);
            fToRhss.put(f, fUsableSyms);
            fCalledIncr.put(f, Boolean.FALSE);
            fCalledDecr.put(f, Boolean.FALSE);
        }

        // 4) now get going with the defined rhs symbols of P:
        for (final Pair<FunctionSymbol, Dependence> gAndDep : pUsableSyms) {
            final FunctionSymbol g = gAndDep.x;
            final Dependence dep = gAndDep.y;
            QDPNonMonReductionPairProcessor.computeGUSteps(g, dep, fToRhss, fCalledIncr, fCalledDecr);
        }

        // 5) extract the obtained info from fCalledIncr and fCalledDecr
        final Map<Rule, Direction> res = new LinkedHashMap<Rule, Direction>(r.size());
        for (final Entry<FunctionSymbol, Boolean> fIncr : fCalledIncr.entrySet()) {
            final FunctionSymbol f = fIncr.getKey();
            final boolean normal = fIncr.getValue();
            final boolean reverse = fCalledDecr.get(f);
            final Direction dir = normal ? (reverse ? Direction.Both     : Direction.Normal)
                                   : (reverse ? Direction.Reversed : Direction.None);
            for (final Rule fRule : ruleMap.get(f)) {
                if (dir != Direction.None) { // TODO omit them altogether?
                    res.put(fRule, dir);
                }
            }
        }
        return res;
    }

    /**
     * Computes for a set of rules with which dependences the
     * defined symbols in the rhss of the rules occur.
     *
     * @param rules - defined symbols in their rhss are regarded here
     * @param defSymbols - which symbols are defined?
     * @param eafs - dependences of symbols
     * @return [(function symbol that occurs in a rhs of some rule in rules,
     *           the dependence with which it occurs there)]
     */
    private static Set<Pair<FunctionSymbol, Dependence>> computeDependencesForRules(final Collection<Rule> rules,
            final Set<FunctionSymbol> defSymbols, final ExtendedAfs eafs) {
        final Set<Pair<FunctionSymbol, Dependence>> result = new LinkedHashSet<Pair<FunctionSymbol, Dependence>>();
        for (final Rule rule : rules) {
            final TRSTerm rhs = rule.getRight();
            final Collection<Pair<Position, TRSTerm>> posSubs = rhs.getPositionsWithSubTerms();
            for (final Pair<Position, TRSTerm> posSub : posSubs) {
                final TRSTerm sub = posSub.y;
                if (! posSub.y.isVariable()) {
                    final TRSFunctionApplication fApp = (TRSFunctionApplication) sub;
                    final FunctionSymbol f = fApp.getRootSymbol();
                    if (defSymbols.contains(f)) {
                        // whoopee. found one. now check its dependence.
                        final Dependence d = QDPNonMonReductionPairProcessor.checkDependence(rhs, posSub.x, eafs);
                        result.add(new Pair<FunctionSymbol, Dependence>(f, d));
                    }
                }
            }
        }
        return result;
    }

    /**
     * On termination of the method, fCalledIncr and fCalledDecr will
     * (hopefully) contain additional info for the defined symbols
     * whether their rules must be oriented by >= and/or by "<=" due
     * to the call to g with Dependence dep.
     *
     * @param g - defined symbol in a rhs of a freshly included rule
     *  (or of rhs of a pair)
     * @param dep - dependency of the call to g (i.e., is the root
     *  of the lhs of the rule where g is called incr, decr, wild,
     *  or irrelevant?)
     * @param fToRhss - maps a symbol to the definded symbols in the rhss
     *  of its rules together with the dependences of the symbols at the
     *  respective positions (must be completely initialized before the call)
     * @param fCalledIncr - have the "f(...) -> r" rules been included
     *  as to be oriented by ">="?
     *  => will be updated by computeGUSteps, assumed to be initialized as
     *     mapping all syms in the signature to "false"
     * @param fCalledDecr - have the "f(...) -> r" rules been included
     *  as to be oriented by "<="?
     *  => will be updated by computeGUSteps, assumed to be initialized as
     *     mapping all syms in the signature to "false"
     */
    private static void computeGUSteps(final FunctionSymbol g, final Dependence dep,
            final Map<FunctionSymbol, Set<Pair<FunctionSymbol, Dependence>>> fToRhss,
            final Map<FunctionSymbol, Boolean> fCalledIncr,
            final Map<FunctionSymbol, Boolean> fCalledDecr) {
        // ok, g is called with dependence dep.
        // do we still have to regard the usable rules for g in normal direction?
        switch (dep) {
        case None:
            // nothing to do here :)
            break;
        case Incr:
            // call from increasing lhs
            // => check if the rules of g are known to have to be oriented by ">="
            final boolean gAlreadyCalledIncr = fCalledIncr.get(g);
            if (! gAlreadyCalledIncr) {
                // we are taking care of the calls to g by increasing lhs roots,
                // remember this so this is done once only
                fCalledIncr.put(g, Boolean.TRUE);
                // ok, regard all symbols h called in rhss of g in Incr
                final Set<Pair<FunctionSymbol, Dependence>> symsWithDeps = fToRhss.get(g);
                for (final Pair<FunctionSymbol, Dependence> symWithDep : symsWithDeps) {
                    final FunctionSymbol h = symWithDep.getKey();
                    final Dependence hDep = symWithDep.getValue();
                    // So h is called in Incr, and it is at a position with Dependence hDep.
                    // Since it is called with Incr (the "usual dependence"), only hDep matters.
                    final Dependence resultingDep = hDep;
                    QDPNonMonReductionPairProcessor.computeGUSteps(h, resultingDep, fToRhss, fCalledIncr, fCalledDecr);
                }

            }
            // else: the case has already been taken care of, do nothing
            break;
        case Decr:
            // call from decreasing lhs
            // => check if the rules of g are known to have to be oriented by "<="
            final boolean gAlreadyCalledDecr = fCalledDecr.get(g);
            if (! gAlreadyCalledDecr) {
                // we are taking care of the calls to g by increasing lhs roots,
                // remember this so this is done once only
                fCalledDecr.put(g, Boolean.TRUE);
                // ok, regard all symbols h called in rhss of g in Incr
                final Set<Pair<FunctionSymbol, Dependence>> symsWithDeps = fToRhss.get(g);
                for (final Pair<FunctionSymbol, Dependence> symWithDep : symsWithDeps) {
                    final FunctionSymbol h = symWithDep.getKey();
                    final Dependence hDep = symWithDep.getValue();
                    // So h is called in Decr, and it is at a position with Dependence hDep.
                    // Since it is called with Decr (the "inverse dependence"),
                    // the resulting dependence is the "dual dependence" of hDep.
                    Dependence resultingDep;
                    switch (hDep) {
                    case None:
                        resultingDep = Dependence.None;
                        break;
                    case Incr:
                        resultingDep = Dependence.Decr;
                        break;
                    case Decr:
                        resultingDep = Dependence.Incr;
                        break;
                    case Wild:
                        resultingDep = Dependence.Wild;
                        break;
                    default:
                        throw new RuntimeException("Unknown Dependence " + hDep);
                    }
                    QDPNonMonReductionPairProcessor.computeGUSteps(h, resultingDep, fToRhss, fCalledIncr, fCalledDecr);
                }
            }
            // else: the case has already been taken care of, do nothing
            break;
        case Wild:
            // do not reinvent the wheel, "wild" means that both calls from
            // incr and from decr must be regarded
            QDPNonMonReductionPairProcessor.computeGUSteps(g, Dependence.Incr, fToRhss, fCalledIncr, fCalledDecr);
            QDPNonMonReductionPairProcessor.computeGUSteps(g, Dependence.Decr, fToRhss, fCalledIncr, fCalledDecr);
            break;
        default:
            throw new RuntimeException("Unknown Dependence " + dep);
        }
    }


    /**
     * In the paper, this method is referred to as \mu(t, q).
     *
     * Feed with sane values: The position q must exist in t,
     * and eafs is assumed to know the function symbols on the
     * path to q in t.
     *
     * @param t
     * @param q
     * @param eafs gives \mu(f, i)
     * @return the dependence of the subterm of t at position q
     */
    private static Dependence checkDependence(final TRSTerm t, final Position q, final ExtendedAfs eafs) {
        if (q.isEmptyPosition()) {
            return Dependence.Incr;
        }

        // q has the form i.p
        final int i = q.firstIndex();
        final Position p = q.tail(1);
        if (Globals.useAssertions) {
            assert ! t.isVariable();
        }
        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final TRSTerm ti = fApp.getArgument(i);
        final FunctionSymbol f = fApp.getRootSymbol();

        final Dependence depOfF  = eafs.filterPosition(f, i);
        if (depOfF == Dependence.None) {
            // no need to compute defOfTI :)
            return Dependence.None;
        }
        final Dependence depOfTI = QDPNonMonReductionPairProcessor.checkDependence(ti, p, eafs);
        switch (depOfTI) {
        case None:
            return Dependence.None;
        case Incr:
            if (depOfF == Dependence.Incr) {
                return Dependence.Incr;
            }
            if (depOfF == Dependence.Decr) {
                return Dependence.Decr;
            }
            return Dependence.Wild;
        case Decr:
            if (depOfF == Dependence.Incr) {
                return Dependence.Decr;
            }
            if (depOfF == Dependence.Decr) {
                return Dependence.Incr;
            }
            return Dependence.Wild;
        case Wild:
            return Dependence.Wild;
        default:
            throw new RuntimeException("What kind of Dependence is " +
                    depOfTI + "?!");
        }
    }

    private static class NonMonReductionPairProof extends QDPProof {

        /**
         * The interpretation without diophantine variables.
         */
        private final NonMonPOLO order;

        /**
         * The P rules in the QDPProblem that are oriented strictly.
         */
        private final Set<Rule> strictPRules;

        /**
         * The P rules in the QDPProblem that are oriented weakly.
         */
        private final Set<Rule> keptPRules;

        /**
         * The usable rules that are oriented weakly.
         */
        private final Map<Rule, Direction> usableRules;

        private final QDPProblem origQDP;
        private final QDPProblem resultingQDP;


        /**
         * @param order - the used NonMonPOLO
         * @param strictPRules - The P rules that are oriented strictly.
         * @param keptPRules - The P rules that are oriented weakly.
         * @param usableRules - Information about the usable rules, including
         *  direction (assumed not to contain rules with direction "None").
         */
        public NonMonReductionPairProof(
                final NonMonPOLO order,
                final Set<Rule> strictPRules,
                final Set<Rule> keptPRules,
                final Map<Rule, Direction> usableRules,
                final QDPProblem origQDP,
                final QDPProblem resultingQDP) {
            this.order = order;
            this.strictPRules = strictPRules;
            this.keptPRules = keptPRules;
            this.usableRules = usableRules;
            this.origQDP = origQDP;
            this.resultingQDP = resultingQDP;
        }

        /**
         * Generate the string representing the proof.
         * @param o The export util for special symbols.
         * @param level The verbosity level.
         * @return The proof as a string.
         */
        @Override
        public String export(final Export_Util o,
                final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Using the following max-polynomial ordering, we can ");
            sb.append("orient the general usable rules and all rules ");
            sb.append("from P weakly and some rules from P strictly:");
            sb.append(o.newline());
            sb.append(this.order.export(o));
            sb.append(o.newline());
            sb.append("The following pairs can be oriented strictly and are deleted.");
            sb.append(o.cond_linebreak());
            sb.append(o.set(this.strictPRules, Export_Util.RULES));
            sb.append("The remaining pairs can at least be oriented weakly.");
            sb.append(o.cond_linebreak());
            sb.append(o.set(this.keptPRules, Export_Util.RULES));

            if (this.usableRules.isEmpty()) {
                sb.append("There are no usable rules.");
            } else {
                sb.append("The following rules are usable:");
                final List<String> usables =
                    new ArrayList<String>(this.usableRules.size());
                for (final Entry<Rule, Direction> usable
                        : this.usableRules.entrySet()) {
                    final Rule rule = usable.getKey();
                    final Direction dir = usable.getValue();
                    TRSTerm left, right;
                    if (dir == Direction.Reversed) {
                        left = rule.getRight();
                        right = rule.getLeft();
                    } else {
                        left = rule.getLeft();
                        right = rule.getRight();
                    }
                    final String s = left.export(o) + " " + (dir == Direction.Both
                            ? o.leftrightarrow() : o.rightarrow())
                      + " " + right.export(o);
                    usables.add(s);
                }
                sb.append(o.set(usables, Export_Util.RULES));
            }
            return sb.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                if (this.order.isCPFSupported() == null) { // currently false, but the remaining code can already be written
                    final FunctionSymbol f = FunctionSymbol.create("someNewFreshSymbol", 0);
                    // the symbol should be interpreted by 0 (in fact, the symbol does not have to be fresh, it just has to be interpreted by 0
                    // TODO: this requirement must be passed into the order, or one should patch the generated order-element
                    final Element conditions = CPFTag.CONDITIONS.create(doc);
                    for (final Rule dp : this.origQDP.getP()) {
                        conditions.appendChild(CPFTag.CONDITION.create(doc,
                                CPFTag.CONDITIONAL_CONSTRAINT.create(doc,
                                        CPFTag.CONSTRAINT.create(doc,
                                                dp.getLeft().toCPF(doc, xmlMetaData),
                                                (this.keptPRules.contains(dp) ? CPFTag.NON_STRICT : CPFTag.STRICT).create(doc),
                                                dp.getRight().toCPF(doc, xmlMetaData))),
                                CPFTag.DP_SEQUENCE.create(doc,
                                        CPFTag.RULES.create(doc, dp.toCPF(doc, xmlMetaData))),
                                CPFTag.CONDITIONAL_CONSTRAINT_PROOF.create(doc,
                                        CPFTag.FINAL.create(doc))));
                    }
                    final Element condRedpairProof = CPFTag.COND_RED_PAIR_PROOF.create(doc,
                            f.toCPF(doc, xmlMetaData),
                            CPFTag.BEFORE.create(doc, doc.createTextNode("" + 0)),
                            CPFTag.AFTER.create(doc, doc.createTextNode("" + 0)),
                            conditions
                            );
                    return CPFTag.DP_PROOF.create(doc,
                            CPFTag.GENERAL_RED_PAIR_PROC.create(doc,
                                    this.order.toCPF(doc, xmlMetaData),
                                    CPFTag.STRICT.create(doc, CPFTag.rules(doc, xmlMetaData, this.strictPRules)),
                                    CPFTag.BOUND.create(doc, CPFTag.rules(doc, xmlMetaData, this.origQDP.getP())),
                                    condRedpairProof,
                                    childrenProofs[0]
                                    ));
                } else {
                    return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
                }
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultingQDP);
            }
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !(modus.isPositive() && this.order.isCPFSupported() != null);
        }

    }

    public static class Arguments {
        public boolean allstrict = false;
        public Engine engine;
        public NonMonPOLOFactory.Heuristic heuristic;
        public int negRange;
        public int posRange;
        public DiophantineSATConverter satConverter;
    }
}
