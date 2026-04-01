package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.ConditionalRule;
import aprove.verification.dpframework.DPProblem.TheoremProver.TheoremProverRunners.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Inductive theorem proving meets dependency pairs.<p>
 *
 * In detail:
 * -> CADE'09 paper by Swiderski, Parting, Giesl, Fuhs, Schneider-Kamp.<p>
 *
 * In more detail:
 * -> Michael Parting's diploma thesis.<p>
 *
 * In detail with ACL2:
 * -> JAR'11 paper by Fuhs, Giesl, Parting, Schneider-Kamp, Swiderski.
 *
 * @author micpar
 */
public class QDPTheoremProverProcessor extends Processor.ProcessorSkeleton {

    // none of these Strings should be a prefix of another
    public final static String BOOL_SORT = "bool";
    public final static String SORT_VAR_PREFIX = "a";
    public final static String SORT_PREFIX = "sort";

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPTheoremProverProcessor");
    /*
     * attributes
     */
    private final SolverFactory solverFactory;
    private final String theoremProverStrategy;
    private final String theoremProverTimeLimit;
    private final boolean unpackConstructors;
    private final boolean removeDuplicates;
    private final TheoremProverRunner runner;
    private final RuleHeuristic ruleHeuristic;

    public enum RuleHeuristic {
        ANY_RULE, // used for the CADE'09 paper
        SMALL_OR_LAST_CALL; // candidate for JAR'11
    }

    @ParamsViaArgumentObject
    public QDPTheoremProverProcessor(final Arguments arguments) {
        this.solverFactory = arguments.order;
        this.theoremProverStrategy = arguments.theoremProverStrategy;
        this.theoremProverTimeLimit = arguments.theoremProverTimeLimit;
        this.unpackConstructors = arguments.unpackConstructors;
        this.removeDuplicates = arguments.removeDuplicates;
        this.runner = arguments.runner;
        this.ruleHeuristic = arguments.ruleHeuristic;
    }

    /**
     * @param obl
     * @return whether obl is an "innermost" QDPProblem where R and P are
     *  left-linear constructor systems and where R is non-overlapping
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        // Ensure QDP-Problem
        if (!(obl instanceof QDPProblem)) {
            return false;
        }
        final QDPProblem qdp = (QDPProblem) obl;
        return QDPTheoremProverProcessor.isThmProverApplicable(qdp);
    }

    /**
     * @param qdp
     * @return whether qdp is an "innermost" QDPProblem where R and P are
     *  left-linear constructor systems and where R is non-overlapping
     */
    public static boolean isThmProverApplicable(final QDPProblem qdp) {
        // Ensure (subset of) innermost rewrite relation
        if (!qdp.getInnermost()) {
            return false;
        }

        // Ensure tuple property
        if (CollectionUtils.getTupleSymbols(qdp.getP(), qdp.getR()) == null) {
            return false;
        }

        RuleAnalysis<Rule> analysis = new RuleAnalysis<Rule>(qdp.getR(), IDPPredefinedMap.EMPTY_MAP);
        Set<FunctionSymbol> defSyms = analysis.getDefinedSymbols();
        for (final Rule rule : qdp.getR()) {
            // Ensure left linearity
            if (!rule.getLeft().isLinear()) {
                return false;
            }
            // Ensure constructor system
            final Set<FunctionSymbol> leftArgSyms = CollectionUtils.getFunctionSymbols(rule.getLeft().getArguments());
            leftArgSyms.retainAll(defSyms);
            if (!leftArgSyms.isEmpty()) {
                return false;
            }
        }
        analysis = new RuleAnalysis<Rule>(qdp.getP(), IDPPredefinedMap.EMPTY_MAP);
        defSyms = analysis.getDefinedSymbols();
        for (final Rule rule : qdp.getP()) {
            // Ensure left linearity
            if (!rule.getLeft().isLinear()) {
                return false;
            }
            // Ensure constructor system
            final Set<FunctionSymbol> leftArgSyms = CollectionUtils.getFunctionSymbols(rule.getLeft().getArguments());
            leftArgSyms.retainAll(defSyms);
            if (!leftArgSyms.isEmpty()) {
                return false;
            }
        }

        // Ensure that R is not overlapping
        if (CollectionUtils.isOverlapping(qdp.getR())) {
            return false;
        }

        // Ensure that LHSs of P have no critical pairs with R
        if (QDPTheoremProverProcessor.isPRoverlapping(qdp)) {
            return false;
        }
        return true;
    }

    /**
     * @param qdp - a QDPProblem with the tuple property (the symbols on
     *  roots of LHSs and RHSs of P do not occur anywhere else in R or P,
     *  and, of course, no rule from P has a variable as RHS)
     * @return if there is a rule s -> t in P such that a proper subterm of s
     *  unifies (var-disjointly) with a LHS of a rule from R
     */
    private static boolean isPRoverlapping(final QDPProblem qdp) {
        final Set<Rule> P = qdp.getP();
        final Set<Rule> R = qdp.getR();
        final Set<TRSFunctionApplication> pLhss = CollectionUtils.getLeftHandSides(P);
        final Set<TRSTerm> pNonVarSubterms = new LinkedHashSet<TRSTerm>();
        for (final TRSFunctionApplication pLhs : pLhss) {
            for (final TRSTerm lhsArg : pLhs.getArguments()) {
                pNonVarSubterms.addAll(lhsArg.getNonVariableSubTerms());
            }
        }
        for (final Rule rRule : R) {
            final TRSTerm rLeft = rRule.getLeft();
            for (final TRSTerm pSubterm : pNonVarSubterms) {
                if (rLeft.unifiesVarDisjoint(pSubterm)) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        try {
            return doProcess(obl, aborter, rti);
        } catch (TheoremProverFailedException e) {
            return ResultFactory.error(e);
        }
    }

    private Result doProcess(final BasicObligation obl,
                             final Abortion aborter,
                             final RuntimeInformation rti) throws AbortionException, TheoremProverFailedException {
        final QDPProblem qdp = (QDPProblem) obl;
        // Make sure the variables of the DPs are disjoint
        final Set<Rule> DPs = new LinkedHashSet<Rule>();
        final Set<TRSVariable> forbiddenVars = new LinkedHashSet<TRSVariable>();
        for (Rule dp : qdp.getP()) {
            dp = dp.renameVariables(forbiddenVars);
            DPs.add(dp);
            forbiddenVars.addAll(dp.getVariables());
        }
        final ImmutableSet<Rule> protoP = ImmutableCreator.create(DPs);
        final ImmutableSet<Rule> protoR = this.usableFunctionsFromRAndPWithNewVars(qdp.getR(), protoP, forbiddenVars);

        // now there are no two different rules in protoP \cup protoR
        // which have a variable in common, and all their variables
        // are in forbiddenVars

        // based on protoR and protoP, we can now initialize the NameManager
        final Set<FunctionSymbol> fSyms = qdp.getPRSignature();
        final NameManager nameManager = NameManager.create(fSyms, forbiddenVars);

        // cleanse input from names clashing with predefined TheoremProver names
        final Pair<ImmutableSet<Rule>, Map<Rule, Rule>> PWithCleanToOriginal = nameManager.cleanSymbolsInRules(protoP);
        final Pair<ImmutableSet<Rule>, Map<Rule, Rule>> RWithCleanToOriginal = nameManager.cleanSymbolsInRules(protoR);
        final ImmutableSet<Rule> P = PWithCleanToOriginal.x;
        final ImmutableSet<Rule> R = RWithCleanToOriginal.x;
        nextdp: for (final Rule selectedDP : P) {
            if (selectedDP.getRight().getFunctionSymbols().isEmpty()) {
                continue nextdp;
            }
            QDPTheoremProverProcessor.log.log(Level.FINE, "selected DP: " + selectedDP.toString());

            // Here we know that selectedDPs has at exactly one element
            final TRSFunctionApplication dpRhs = (TRSFunctionApplication) selectedDP.getRight();

            MonotonicityConstraints monCon = null;
            ImmutableSet<Rule> strictDecreasing = null;
            Set<Integer> dpMonArgs = new LinkedHashSet<Integer>();

            int count = Math.min(2, dpRhs.getArguments().size());
            while (count > 0) {
                count--;
                ImmutableSet<Rule> usableRules = R;
                final ImmutableSet<Rule> candidates = this.usableFunctions(usableRules, dpRhs.getFunctionSymbols());

                if (usableRules.isEmpty()) {
                    continue nextdp;
                }

                final Set<Rule> typeInferenceRules = new LinkedHashSet<Rule>(usableRules);
                typeInferenceRules.addAll(P);
                final ImmutableSet<Rule> immutableTypeInferenceRules = ImmutableCreator.create(typeInferenceRules);
                // Calculate TypeAssumption and sorts
                final TypeAssumptionCalculator typeAssumptioncalculator = new TypeAssumptionCalculator();
                final TypeAssumption typeAssumption =
                    typeAssumptioncalculator.calculateTypeAssumption(immutableTypeInferenceRules);
                final SortCalculator sortCalculator =
                    new SortCalculator(typeAssumption, immutableTypeInferenceRules, nameManager);

                // Check if usableRules are complete and complete them with
                // witness terms if necessary
                final RuleCompletion ruleCom = RuleCompletion.create(usableRules, sortCalculator, nameManager);
                usableRules = ruleCom.completeRules();

                if (monCon != null) {
                    dpMonArgs = new LinkedHashSet<Integer>(monCon.getConstraint(dpRhs.getRootSymbol()));
                    if (dpMonArgs.contains(0) ^ dpMonArgs.contains(1)) {
                        if (dpMonArgs.contains(0)) {
                            dpMonArgs.clear();
                            dpMonArgs.add(1);
                        } else {
                            dpMonArgs.clear();
                            dpMonArgs.add(0);
                        }
                    }
                }
                // Speculate decreasing rule and add it as only strictness
                // candidate
                final DecreasingRuleSpeculator drs = new DecreasingRuleSpeculator(this.ruleHeuristic);
                final Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> resultOrder =
                    drs.calculateDecreasingRulesWithPOLO(usableRules, dpRhs, this.solverFactory, P, aborter, QDPTheoremProverProcessor.log,
                        ImmutableCreator.create(dpMonArgs), strictDecreasing, candidates);
                // Could not successfully speculate a decreasing rule, proceed
                // with next DP
                if (resultOrder == null) {
                    // When we reach this point we know that no rule is suitable
                    // as decreasing rule and we need to check another DP
                    QDPTheoremProverProcessor.log.log(Level.FINE, "No suitable order found.");
                    continue nextdp;
                }
                strictDecreasing = resultOrder.getX();
                QDPTheoremProverProcessor.log.log(Level.FINE, "These are the strictly decreasing rules: " + strictDecreasing);

                // Monotonicity constraints for strictness candidate
                monCon = resultOrder.getY();

                // Filter out non monotonic arguments of the DP as well as
                // variables
                // and constructor terms
                final RuleAnalysis<Rule> analysis = new RuleAnalysis<Rule>(usableRules, IDPPredefinedMap.EMPTY_MAP);
                final Set<FunctionSymbol> defSyms = analysis.getDefinedSymbols();
                final ArrayList<TRSTerm> dpArgs = new ArrayList<TRSTerm>(dpRhs.getArguments());
                final Iterator<TRSTerm> argIter = dpArgs.iterator();
                int index = 0;
                while (argIter.hasNext()) {
                    final TRSTerm argument = argIter.next();
                    final Set<FunctionSymbol> definedSymbolsInArgument = argument.getFunctionSymbols();
                    definedSymbolsInArgument.retainAll(defSyms);
                    if (definedSymbolsInArgument.isEmpty()) {
                        argIter.remove();

                    } else if (!monCon.getConstraint(dpRhs.getRootSymbol()).contains(index)) {
                        argIter.remove();
                    }
                    index++;
                }
                if (dpArgs.isEmpty()) {
                    // When we reach this point we know that the DP is not
                    // suitable for our proof
                    continue nextdp;
                }
                // Add rules for the theorem prover to usableRules
                final RuleTransformation ruleTran =
                    RuleTransformation.create(usableRules, strictDecreasing, ImmutableCreator.create(dpArgs), monCon,
                        sortCalculator, nameManager);
                usableRules = ruleTran.applyChainRuleTransformation();
                ImmutableSet<ConditionalRule> condUsableRules =
                    ImmutableCreator.create(ConditionalRule.create(usableRules));
                // Narrow down rules
                final SimpleNarrowing simpleNarrowing = new SimpleNarrowing(sortCalculator, nameManager);
                condUsableRules = simpleNarrowing.narrowRules(condUsableRules);

                // Create and initialize program object here
                final ProgramInitializer prgrmInit =
                    ProgramInitializer.create(condUsableRules, sortCalculator, nameManager);
                final Program prgrm = prgrmInit.createAndInitializeProgram();

                // Extract the equality functions and all the other functions
                // created within the Program object, because this stuff must
                // terminate too.
                final Set<Rule> tempUsableRules = new LinkedHashSet<Rule>(usableRules);
                outer: for (final aprove.verification.oldframework.Rewriting.Rule rule : prgrm.getAllRules()) {
                    final Rule newRule = rule.toNewRule();
                    for (final Rule usableRule : usableRules) {
                        if (usableRule.getRootSymbol().getName().equals(newRule.getRootSymbol().getName())) {
                            continue outer;
                        }
                    }
                    tempUsableRules.add(newRule);
                }
                usableRules = ImmutableCreator.create(tempUsableRules);

                // Create formula for the theorem prover here
                final FormulaCreator frmlcreator = new FormulaCreator(nameManager);
                final Formula frml =
                    frmlcreator.createFormula(ruleTran.getTransformedDPArguments(), prgrm, usableRules, sortCalculator,
                        this.unpackConstructors, this.removeDuplicates);

                // Run theorem prover on processed program and formula
                QDPTheoremProverProcessor.log.log(Level.FINE, "Trying to prove validity of the formula: " + frml);
                final Pair<Boolean, Exportable> result =
                    this.runner.runTheoremProverOnInput(frml, prgrm, this.theoremProverStrategy,
                        this.theoremProverTimeLimit, aborter, rti);
                final boolean theoremProverSaysYes = result.x;
                if (theoremProverSaysYes) {
                    QDPTheoremProverProcessor.log.log(Level.FINE, "SUCCESS: The formula " + frml + " is valid.");
                    if (Globals.DEBUG_FUHS) {
                        System.err.println("SUCCESS: The formula " + frml + " is valid.");
                    }
                    // Create results : success!
                    final Set<Rule> newP = new LinkedHashSet<Rule>(qdp.getP());

                    // remember the predefinied symbol cleaning
                    final Rule removedDP = PWithCleanToOriginal.y.get(selectedDP);
                    newP.remove(removedDP);
                    final QDPProblem newQdp = qdp.getSubProblem(newP, qdp.getR());
                    final QTRSProblem qtrsp = QTRSProblem.create(usableRules);
                    final List<DefaultBasicObligation> todos = new ArrayList<>(2);
                    todos.add(newQdp);
                    todos.add(qtrsp);
                    return ResultFactory.provedAnd(todos, YNMImplication.SOUND, new QDPTheoremProverProof(
                        qdp,
                        newQdp,
                        qtrsp,
                        resultOrder,
                        usableRules, selectedDP, frml, result.y));
                }
                QDPTheoremProverProcessor.log.log(Level.FINE, "FAILURE: Proof of " + frml + " failed.");
            }
        }
        // When we reach this point, we know that no rule and no DP is suitable
        // to prove everything
        // Create results : failure!
        QDPTheoremProverProcessor.log.log(Level.INFO, "The QDP-Theorem-Prover-Processor could not delete any DP.");
        return ResultFactory.unsuccessful();
    }

    private ImmutableSet<Rule> usableFunctionsFromRAndPWithNewVars(final ImmutableSet<Rule> R,
        final ImmutableSet<Rule> P,
        final Set<TRSVariable> forbiddenVars) {
        final Set<FunctionSymbol> funSyms = new LinkedHashSet<FunctionSymbol>();
        for (final Rule rule : P) {
            funSyms.addAll(rule.getFunctionSymbols());
            funSyms.remove(rule.getLeft().getRootSymbol());
            funSyms.remove(((TRSFunctionApplication) rule.getRight()).getRootSymbol());
        }
        return this.usableFunctionsWithNewVars(R, funSyms, forbiddenVars);
    }

    private ImmutableSet<Rule> usableFunctionsWithNewVars(final ImmutableSet<Rule> rules,
        final Set<FunctionSymbol> funSyms,
        final Set<TRSVariable> forbiddenVars) {
        final Set<Rule> usableRules = new LinkedHashSet<Rule>();
        final List<Rule> notYetAddedRules = new LinkedList<Rule>(rules);
        boolean funSymAdded;
        do {
            funSymAdded = false;
            final Iterator<Rule> iter = notYetAddedRules.iterator();
            while (iter.hasNext()) {
                final Rule rule = iter.next();
                if (funSyms.contains(rule.getRootSymbol())) {
                    iter.remove();
                    final Rule newRule = rule.renameVariables(forbiddenVars);
                    forbiddenVars.addAll(newRule.getVariables());
                    funSymAdded = usableRules.add(newRule) || funSymAdded;
                    funSyms.addAll(newRule.getRight().getFunctionSymbols());
                }
            }
        } while (funSymAdded);
        return ImmutableCreator.create(usableRules);
    }

    private ImmutableSet<Rule> usableFunctions(final ImmutableSet<Rule> rules, final Set<FunctionSymbol> funSyms) {
        final Set<Rule> usableRules = new LinkedHashSet<Rule>();
        final List<Rule> notYetAddedRules = new LinkedList<Rule>(rules);
        boolean funSymAdded;
        do {
            funSymAdded = false;
            final Iterator<Rule> iter = notYetAddedRules.iterator();
            while (iter.hasNext()) {
                final Rule rule = iter.next();
                if (funSyms.contains(rule.getRootSymbol())) {
                    iter.remove();
                    funSymAdded = usableRules.add(rule) || funSymAdded;
                    funSyms.addAll(rule.getRight().getFunctionSymbols());
                }
            }
        } while (funSymAdded);
        return ImmutableCreator.create(usableRules);
    }

    public static class Arguments {
        public SolverFactory order;
        public String theoremProverStrategy;
        public String theoremProverTimeLimit;
        public boolean unpackConstructors = false;
        public boolean removeDuplicates = false;
        public TheoremProverRunner runner = new AproveRunner();
        public RuleHeuristic ruleHeuristic = RuleHeuristic.ANY_RULE;
    }

}

class QDPTheoremProverProof extends QDPProof {

    Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> resultOrder = null;
    ImmutableSet<Rule> usableRules = null;
    Rule selectedDP = null;
    Formula frml = null;
    Exportable runnerProof = null;
    QDPProblem origQDP, newQDP;
    QTRSProblem newQtrs;

    public QDPTheoremProverProof(
        final QDPProblem origQDP,
        final QDPProblem newQDP,
        final QTRSProblem newQtrs,
            final Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> resultOrder,
            final ImmutableSet<Rule> usableRules, final Rule selectedDP, final Formula frml,
            final Exportable runnerProof) {
        this.longName = "Induction-Processor";
        this.shortName = "Induction-Processor";
        this.resultOrder = resultOrder;
        this.usableRules = usableRules;
        this.selectedDP = selectedDP;
        this.frml = frml;
        this.runnerProof = runnerProof;
        this.origQDP = origQDP;
        this.newQDP = newQDP;
        this.newQtrs = newQtrs;
    }

    @Override
    public String export(final Export_Util o, final VerbosityLevel level) {
        final StringBuilder result = new StringBuilder();
        result.append(o.linebreak());
        if (this.selectedDP != null) {
            result.append(o.bold("This DP could be deleted by the Induction-Processor:"));
            result.append(o.linebreak());
            result.append(o.export(this.selectedDP));
            result.append(o.linebreak());
        }
        if (this.resultOrder != null) {
            result.append(o.linebreak());
            result.append(o.cond_linebreak());
            result.append(o.bold("This order was computed:"));
            result.append(o.linebreak());
            result.append(o.export(this.resultOrder.getZ()));
            result.append(o.linebreak());
            //result.append(o.bold("These monotonicity constraints hold:"));
            //result.append(o.linebreak());
            //result.append(o.export(this.resultOrder.getY()));
            //result.append(o.linebreak());
            result.append(o.bold("At least one of these decreasing rules is always used after the deleted DP:"));
            result.append(o.linebreak());
            for (final Rule rule : this.resultOrder.getX()) {
                result.append(o.export(rule));
                result.append(o.linebreak());
            }
        }
        if (this.frml != null) {
            result.append(o.linebreak());
            result.append(o.cond_linebreak());
            result.append(o.bold("The following formula is valid:"));
            result.append(o.linebreak());
            result.append(o.export(this.frml));
            result.append(o.linebreak());
        }
        if (this.usableRules != null) {
            result.append(o.linebreak());
            result.append(o.cond_linebreak());
            result.append(o.bold("The transformed set:"));
            result.append(o.linebreak());
            for (final Rule rule : this.usableRules) {
                result.append(o.export(rule));
                result.append(o.linebreak());
            }
        }
        if (this.runnerProof != null) {
            result.append(o.linebreak());
            result.append(o.cond_linebreak());
            result.append(o.bold("The proof given by the theorem prover:"));
            result.append(o.linebreak());
            result.append(o.export(this.runnerProof));
        }

        return result.toString();
    }

    @Override
    public Element toCPF(
        final Document doc,
        final Element[] childrenProofs,
        final XMLMetaData xmlMetaData,
        final CPFModus modus)
    {
        if (this.isCPFCheckableProof(modus)) {
            return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.newQDP);
        } else {
            return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
        }
    }

    @Override
    public boolean isCPFCheckableProof(final CPFModus modus) {
        return !modus.isPositive() && modus.negativeReason() == 0;
    }

}
