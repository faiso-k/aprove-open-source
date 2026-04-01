package aprove.input.Programs.newTrs;

import java.util.*;

import aprove.*;
import aprove.input.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.CpxGTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author patwie
 * @version $Id$
 */
public class ObligationCreator {

    /*
     * Every possible valid information of the input is coded
     * into a number to the power of 2, so the sum of every
     * valid combination is exactly one integer value.
     */
    private final static int bitSimpleRules = 1 << 0;
    private final static int bitQTerms = 1 << 1;
    private final static int bitEquational = 1 << 3;
    private final static int bitRelativeRules = 1 << 4;
    private final static int bitConditionalRules = 1 << 5;
    private final static int bitContextSensitiveRules = 1 << 7;
    private final static int bitPairs = 1 << 8;
    private final static int bitInnermost = 1 << 9;
    private final static int bitOutermost = 1 << 10;
    private final static int bitMinimal = 1 << 11;
    private final static int bitGeneralizedRules = 1 << 12;
    private final static int bitPredefinedSemantics = 1 << 13;
    private final static int bitEdges = 1 << 14;
    private final static int bitComplexity = 1 << 15;
    private final static int bitConstructorbased = 1 << 16;
    private final static int bitParallelInnermost = 1 << 17;

    private static boolean notEmpty(final Collection<?> c) {
        return c != null && !c.isEmpty();
    }

    /*
     * Declaration of the Constructs to which the parser will
     * collect information.
     */
    private Set<String> assAndComFunctionSymbols;
    private Set<String> associativeFunctionSymbols;
    private Set<String> commutativeFunctionSymbols;
    private boolean complexity;
    private Set<ConditionalRule> conditionalRules;
    private boolean constructorbased;
    private Set<Pair<String, Set<Integer>>> contextSensitiveRules;
    private Object domainSemantics = null;
    private Set<Pair<Integer, Integer>> edges;
    private Set<Equation> equations;
    private Set<GeneralizedRule> allRules;
    private boolean innermost;
    private Language language = null;
    private boolean minimal;
    private final List<ParseError> obligationErrors;
    private boolean outermost;
    private boolean parallelInnermost;
    private Set<Rule> pairs;
    private Map<FunctionSymbol, PredefinedFunction<? extends Domain>> predefinedFunctionSemantics = null;
    private Set<TRSFunctionApplication> qFunctionApplications;
    private Set<Rule> relativeRules;
    private Set<Rule> simpleRules;
    private Set<Pair<TRSTerm,TRSTerm>> lhsVariableRelRules;

    public ObligationCreator(final RawTrs fullpass) {
        this.obligationErrors = new LinkedList<ParseError>();
        this.getAll(fullpass);
    }

    public BasicObligation buildObligation() throws ObligationCreatorException {
        final BasicObligation obligation = this.generateProblem();
        if (!this.obligationErrors.isEmpty()) {
            throw new ObligationCreatorException(this.obligationErrors);
        } else {
            return obligation;
        }
    }

    public List<ParseError> getErrors() {
        return this.obligationErrors;
    }

    public Language getLanguage() {
        return this.language;
    }

    private Set<Equation> computeEquations() {
        final Set<FunctionSymbol> FuncSymbolsOfSimpleRules = CollectionUtils.getFunctionSymbols(this.simpleRules);
        final Set<Equation> result = new LinkedHashSet<Equation>();
        if (this.equations != null) {
            result.addAll(this.equations);
        }
        if (ObligationCreator.notEmpty(this.commutativeFunctionSymbols)) {
            result.addAll(OblCreatorEtrs.getCommutativeEquations(
                OblCreatorEtrs.buildSymColl(this.commutativeFunctionSymbols), FuncSymbolsOfSimpleRules));
        }
        if (ObligationCreator.notEmpty(this.associativeFunctionSymbols)) {
            result.addAll(OblCreatorEtrs.getAssociativeEquations(
                OblCreatorEtrs.buildSymColl(this.associativeFunctionSymbols), FuncSymbolsOfSimpleRules));
        }
        if (ObligationCreator.notEmpty(this.assAndComFunctionSymbols)) {
            final Set<FunctionSymbol> buildAssAndComm = OblCreatorEtrs.buildSymColl(this.assAndComFunctionSymbols);
            result.addAll(OblCreatorEtrs.getCommutativeEquations(buildAssAndComm, FuncSymbolsOfSimpleRules));
            result.addAll(OblCreatorEtrs.getAssociativeEquations(buildAssAndComm, FuncSymbolsOfSimpleRules));
        }
        return result;
    }

    private QDPProblem createQDP() {
        final QTRSProblem qtrsProblem = this.getQTRS();
        this.language = Language.QDP;
        return QDPProblem.create(ImmutableCreator.create(this.pairs), qtrsProblem, this.minimal);
    }

    private BasicObligation createVerifiedETRS() {
        final ETRSProblem etrsProblem =
            ETRSProblem.create(
                ImmutableCreator.create(this.simpleRules),
                ImmutableCreator.create(this.computeEquations())
            );
        //At the moment only AC and C Equations are allowed.
        if (etrsProblem.checkACandAandC()) {
            this.language = Language.ETRS;
            return etrsProblem;
        } else {
            final ParseError pe = new ParseError();
            pe.setMessage("Only AC-, A- or C-Equations are supported so far.");
            this.obligationErrors.add(pe);
            this.language = Language.QTRS;
            return null;
        }
    }

    private BasicObligation generateProblem() {
        /* First analyze the given combination.
         * For each existing componenet add the corresponding integer value
         * and save in a String which components have occured for Error handling.
         * Afterwards try to find in the case block a valid combination and build
         * the apropriate proof obligation.
         */
        final boolean relativeNotEmpty = ObligationCreator.notEmpty(this.relativeRules) || ObligationCreator.notEmpty(this.lhsVariableRelRules); 
        final boolean generalizedNotEmpty =
            this.allRules.size() - (this.simpleRules == null ? 0 : this.simpleRules.size()) > 0;
        final boolean conditionalNotEmpty = ObligationCreator.notEmpty(this.conditionalRules);
        final boolean contextSensitiveNotEmpty = ObligationCreator.notEmpty(this.contextSensitiveRules);
        final boolean pairsNotNull = this.pairs != null;
        final boolean qFuncAppsNotNull = this.qFunctionApplications != null;
        final boolean predefFuncSemNotNull = this.predefinedFunctionSemantics != null;
        final boolean domSemNotNull = this.domainSemantics != null;
        final boolean edgesNotNull = this.edges != null;

        final boolean equational =
            ObligationCreator.notEmpty(this.equations)
            | ObligationCreator.notEmpty(this.associativeFunctionSymbols)
            | ObligationCreator.notEmpty(this.commutativeFunctionSymbols)
            | ObligationCreator.notEmpty(this.assAndComFunctionSymbols);

        final int problemValue =
            (this.simpleRules != null ? ObligationCreator.bitSimpleRules : 0)
                | (generalizedNotEmpty ? ObligationCreator.bitGeneralizedRules : 0)
                | (qFuncAppsNotNull ? ObligationCreator.bitQTerms : 0)
                | (equational ? ObligationCreator.bitEquational : 0)
                | (relativeNotEmpty ? ObligationCreator.bitRelativeRules : 0)
                | (conditionalNotEmpty ? ObligationCreator.bitConditionalRules : 0)
                | (contextSensitiveNotEmpty ? ObligationCreator.bitContextSensitiveRules : 0)
                | (pairsNotNull ? ObligationCreator.bitPairs : 0)
                | (this.complexity ? ObligationCreator.bitComplexity : 0)
                | (this.constructorbased ? ObligationCreator.bitConstructorbased : 0)
                | (this.innermost ? ObligationCreator.bitInnermost : 0)
                | (this.parallelInnermost ? ObligationCreator.bitParallelInnermost : 0)
                | (this.outermost ? ObligationCreator.bitOutermost : 0)
                | (this.minimal ? ObligationCreator.bitMinimal : 0)
                | ((predefFuncSemNotNull || domSemNotNull) ? ObligationCreator.bitPredefinedSemantics : 0)
                | (edgesNotNull ? ObligationCreator.bitEdges : 0);

        final String problemCombination =
            (this.simpleRules != null ? "Simple Rules, " : "  ")
                + (generalizedNotEmpty ? "Generalized Rules, " : "")
                + (qFuncAppsNotNull ? "Q-Terms, " : "")
                + (equational ? "Equational, " : "")
                + (relativeNotEmpty ? "Relative Rules, " : "")
                + (conditionalNotEmpty ? "Conditional Rules, " : "")
                + (contextSensitiveNotEmpty ? "Context Sensitive Rules, " : "")
                + (pairsNotNull ? "Pairs, " : "")
                + (this.complexity ? "Complexity Analysis, " : "")
                + (this.constructorbased ? "Constructor-based, " : "")
                + (this.innermost ? "Innermost Obligation, " : "")
                + (this.parallelInnermost ? "Parallel-Innermost Obligation, " : "")
                + (this.outermost ? "Outermost Obligation, " : "")
                + (this.minimal ? "Minimal Obligation, " : "")
                + ((predefFuncSemNotNull || domSemNotNull) ? "Predefined Semantics, " : "")
                + (edgesNotNull ? "Dependency Graph Edges, " : "");

        switch (problemValue) {
        case (ObligationCreator.bitSimpleRules):
        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitQTerms): {
            this.language = Language.QTRS;
            return this.getQTRS();
        }

        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitInnermost):
            this.qFunctionApplications = new LinkedHashSet<TRSFunctionApplication>();
        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitQTerms | ObligationCreator.bitInnermost): {
            this.qFunctionApplications.addAll(CollectionUtils.getLeftHandSides(this.simpleRules));
            this.language = Language.QTRS;
            return this.getQTRS();
        }

        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitRelativeRules): {
            //TODO implement this type!!!
            this.language = Language.RTRS;
            return RelTRSProblem.create((ImmutableCreator.create(this.simpleRules)),
                (ImmutableCreator.create(this.relativeRules)), (ImmutableCreator.create(this.lhsVariableRelRules)));
        }
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitRelativeRules
            | ObligationCreator.bitConstructorbased
            | ObligationCreator.bitComplexity
        ):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitRelativeRules
            | ObligationCreator.bitConstructorbased
            | ObligationCreator.bitComplexity
            | ObligationCreator.bitInnermost
        ):
        case (
                ObligationCreator.bitSimpleRules
                | ObligationCreator.bitRelativeRules
                | ObligationCreator.bitConstructorbased
                | ObligationCreator.bitComplexity
                | ObligationCreator.bitParallelInnermost
        ): {
            this.language = Language.CpxRelTRS;
            return RuntimeComplexityRelTrsProblem.create(ImmutableCreator.create(this.simpleRules),
                ImmutableCreator.create(this.relativeRules),
                this.innermost ? RewriteStrategy.INNERMOST
                    : (this.parallelInnermost ? RewriteStrategy.PARALLEL_INNERMOST : RewriteStrategy.FULL),
                false);
        }
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitRelativeRules
            | ObligationCreator.bitComplexity
        ):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitRelativeRules
            | ObligationCreator.bitComplexity
            | ObligationCreator.bitInnermost
        ):
        case (
                ObligationCreator.bitSimpleRules
                | ObligationCreator.bitRelativeRules
                | ObligationCreator.bitComplexity
                | ObligationCreator.bitParallelInnermost
        ): {
            this.language = Language.CpxRelTRS;
            return DerivationalComplexityRelTrsProblem.create(ImmutableCreator.create(this.simpleRules),
                ImmutableCreator.create(this.relativeRules),
                this.innermost ? RewriteStrategy.INNERMOST
                    : (this.parallelInnermost ? RewriteStrategy.PARALLEL_INNERMOST : RewriteStrategy.FULL),
                false);
            }
        case (ObligationCreator.bitConditionalRules): {
            this.language = Language.CTRS;
            return CTRSProblem.create(ImmutableCreator.create(java.util.Collections.<Rule>emptySet()),
                ImmutableCreator.create(this.conditionalRules));
        }
        case (ObligationCreator.bitSimpleRules + ObligationCreator.bitConditionalRules): {
            this.language = Language.CTRS;
            return CTRSProblem.create(ImmutableCreator.create(this.simpleRules),
                ImmutableCreator.create(this.conditionalRules));
        }
        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitContextSensitiveRules):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitContextSensitiveRules
            | ObligationCreator.bitInnermost
        ): {
            final Set<FunctionSymbol> simpleRulesSignature = CollectionUtils.getFunctionSymbols(this.simpleRules);
            final int nrFs = simpleRulesSignature.size();
            if (Globals.DEBUG_PATWIE) {
                System.err.println("Simple Rules Signature: ");
                for (final FunctionSymbol fs : simpleRulesSignature) {
                    System.err.println(fs.toString());
                }
            }
            final HashMap<String, Integer> checkFunctionArityMap = new HashMap<String, Integer>(nrFs);
            final Map<FunctionSymbol, Set<Integer>> replacementMap = new HashMap<FunctionSymbol, Set<Integer>>(nrFs);
            final Map<String, Set<Integer>> preReplacementMap = new HashMap<String, Set<Integer>>(nrFs);

            // build a replacementMap from Strings to Set<Integer> first
            for (final Pair<String, Set<Integer>> replacement : this.contextSensitiveRules) {
                final String f = replacement.x;
                final Set<Integer> rep = replacement.y;
                final Set<Integer> old = preReplacementMap.put(f, rep);
                if (old != null && !old.equals(rep)) {
                    final ParseError pe = new ParseError();
                    pe.setMessage("Functionsymbol " + f + " has conflicting entries in the replacement map.");
                    this.obligationErrors.add(pe);
                    return null;
                }
            }

            //each function symbol is inserted into the HashMap,
            //if an arity conflict occurs an error is generated
            for (final FunctionSymbol checkedSymbol : simpleRulesSignature) {
                final String checkedSymbolName = checkedSymbol.getName();
                final Integer checkedSymbolArity = checkedSymbol.getArity();
                final Integer arity = checkFunctionArityMap.put(checkedSymbolName, checkedSymbolArity);

                if (arity == null) {
                    // we have seen this symbol the first time
                    final Set<Integer> replacement = preReplacementMap.get(checkedSymbolName);
                    Set<Integer> shiftedRepl;
                    if (replacement == null) {
                        // this means we have an underspecified replacement.
                        // By TPDB convention (H. Zantema) we allow all replacements for these symbols.
                        final int n = checkedSymbolArity;
                        shiftedRepl = new LinkedHashSet<Integer>(n);
                        for (int i = 0; i < n; i++) {
                            shiftedRepl.add(i);
                        }
                    } else {
                        shiftedRepl = new LinkedHashSet<Integer>(replacement.size());
                        for (final Integer i : replacement) {
                            shiftedRepl.add(i - 1);
                        }
                    }
                    replacementMap.put(checkedSymbol, shiftedRepl);
                } else {
                    if (!(arity.equals(checkedSymbolArity))) {
                        final ParseError pe = new ParseError();
                        pe.setMessage("Function Symbol " + checkedSymbolName + " occured with different arity " + "("
                            + arity.toString() + " and " + checkedSymbolArity.toString() + ") !"
                            + "This is not allowed if Context Sensitive Rules are used.");
                        this.obligationErrors.add(pe);
                        return null;
                    }
                }
            }
            this.language = Language.CSR;
            final CSRProblem csr = CSRProblem.create(this.simpleRules, replacementMap, this.innermost);
            return csr;
        }
        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitPairs | ObligationCreator.bitEdges):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitQTerms
            | ObligationCreator.bitPairs
            | ObligationCreator.bitEdges
        ):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitPairs
            | ObligationCreator.bitEdges
            | ObligationCreator.bitMinimal
        ):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitQTerms
            | ObligationCreator.bitPairs
            | ObligationCreator.bitEdges
            | ObligationCreator.bitMinimal
        ): {
            this.language = Language.QDP;
            final QTRSProblem rWithQ = this.getQTRS();
            return QDPProblem.create(rWithQ, this.getDPGraph(rWithQ), this.minimal, true);
        }

        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitPairs):
        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitQTerms | ObligationCreator.bitPairs):
            return this.createQDP();

        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitPairs | ObligationCreator.bitInnermost):
            this.qFunctionApplications = new LinkedHashSet<TRSFunctionApplication>();
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitQTerms
            | ObligationCreator.bitPairs
            | ObligationCreator.bitInnermost
        ): {
            this.qFunctionApplications.addAll(CollectionUtils.getLeftHandSides(this.simpleRules));
            return this.createQDP();
        }

        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitPairs | ObligationCreator.bitMinimal):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitQTerms
            | ObligationCreator.bitPairs
            | ObligationCreator.bitMinimal
        ):
            return this.createQDP();

        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitPairs
            | ObligationCreator.bitInnermost
            | ObligationCreator.bitMinimal
        ):
            this.qFunctionApplications = new LinkedHashSet<TRSFunctionApplication>();
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitQTerms
            | ObligationCreator.bitPairs
            | ObligationCreator.bitInnermost
            | ObligationCreator.bitMinimal
        ): {
            this.qFunctionApplications.addAll(CollectionUtils.getLeftHandSides(this.simpleRules));
            return this.createQDP();
        }

        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitEquational):
            return this.createVerifiedETRS();

        case (ObligationCreator.bitSimpleRules | ObligationCreator.bitOutermost):
        case (ObligationCreator.bitGeneralizedRules | ObligationCreator.bitOutermost):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitGeneralizedRules
            | ObligationCreator.bitOutermost
        ):
            this.language = Language.OTRS;
            return OTRSProblem.create(this.allRules);

        case (ObligationCreator.bitGeneralizedRules | ObligationCreator.bitSimpleRules):
        case (
            ObligationCreator.bitGeneralizedRules
            | ObligationCreator.bitSimpleRules
            | ObligationCreator.bitInnermost
        ):
            this.language = Language.GTRS;
            return GTRSProblem.create(this.allRules, this.innermost);

        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitPredefinedSemantics
            | ObligationCreator.bitInnermost
        ):
        case (
            ObligationCreator.bitGeneralizedRules
            | ObligationCreator.bitPredefinedSemantics
            | ObligationCreator.bitInnermost
        ):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitPredefinedSemantics
            | ObligationCreator.bitInnermost
            | ObligationCreator.bitGeneralizedRules
        ): {
            // ITRS
            /* TODO check that every symbol that has a name occurring in a
             * constant domain has the correct semantics associated
             */
            final ImmutableMap<FunctionSymbol, PredefinedFunction<? extends Domain>> mapping =
                ImmutableCreator.create(this.predefinedFunctionSemantics);
            final Set<GeneralizedRule> genrules = new LinkedHashSet<GeneralizedRule>();
            final Set<TRSFunctionApplication> lhss = new LinkedHashSet<TRSFunctionApplication>();
            final Collection<String> usedFunctionSymbolNames = new LinkedHashSet<String>();
            for (final GeneralizedRule r : this.allRules) {
                genrules.add(r);
                lhss.add(r.getLeft());
                for (final FunctionSymbol f : r.getFunctionSymbols()) {
                    usedFunctionSymbolNames.add(f.getName());
                }
            }
            final IDPPredefinedMap pre = new IDPPredefinedMap(mapping, usedFunctionSymbolNames);
            final ImmutableSet<GeneralizedRule> rules = ImmutableCreator.create(genrules);
            final IQTermSet Q = new IQTermSet(new QTermSet(lhss), pre);
            this.language = Language.ITRS;
            return ITRSProblem.create(rules, Q);
        }

        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitComplexity
            | ObligationCreator.bitConstructorbased
        ):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitComplexity
            | ObligationCreator.bitConstructorbased
            | ObligationCreator.bitInnermost
        ):
        case (
                ObligationCreator.bitSimpleRules
                | ObligationCreator.bitComplexity
                | ObligationCreator.bitConstructorbased
                | ObligationCreator.bitParallelInnermost
        ):
            this.language = Language.CpxTRS;
            return RuntimeComplexityTrsProblem.create(ImmutableCreator.create(this.simpleRules),
                this.innermost ? RewriteStrategy.INNERMOST
                    : (this.parallelInnermost ? RewriteStrategy.PARALLEL_INNERMOST : RewriteStrategy.FULL));

        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitComplexity
            | ObligationCreator.bitConstructorbased
            | ObligationCreator.bitGeneralizedRules
        ):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitComplexity
            | ObligationCreator.bitConstructorbased
            | ObligationCreator.bitInnermost
            | ObligationCreator.bitGeneralizedRules
        ):
            this.language = Language.CpxTRS;
            return new CpxGTrsProblem(this.allRules);

        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitComplexity
        ):
        case (
            ObligationCreator.bitSimpleRules
            | ObligationCreator.bitComplexity
            | ObligationCreator.bitInnermost
        ):
        case (
                ObligationCreator.bitSimpleRules
                | ObligationCreator.bitComplexity
                | ObligationCreator.bitParallelInnermost
        ):
            this.language = Language.CpxTRS;
            return DerivationalComplexityTrsProblem.create(ImmutableCreator.create(this.simpleRules),
                this.innermost ? RewriteStrategy.INNERMOST
                    : (this.parallelInnermost ? RewriteStrategy.PARALLEL_INNERMOST : RewriteStrategy.FULL));

        default: {
            final ParseError pe = new ParseError();
            pe.setMessage(
                "The combination of "
                + problemCombination.substring(0, (problemCombination.length() - 2))
                + " is not allowed!"
            );
            this.obligationErrors.add(pe);
            return null;
        }
        }
    }

    private void getAll(final RawTrs rawtrs) {
        this.simpleRules = rawtrs.getSimpleRules();
        this.allRules = rawtrs.getAllRules();
        this.qFunctionApplications = rawtrs.getQFunctionApplications();
        this.equations = rawtrs.getEquations();
        this.relativeRules = rawtrs.getRelativeRules();
        this.conditionalRules = rawtrs.getConditionalRules();
        this.contextSensitiveRules = rawtrs.getContextSensitiveRules();
        this.pairs = rawtrs.getPairs();
        this.complexity = rawtrs.isComplexity();
        this.constructorbased = rawtrs.isConstructorbased();
        this.innermost = rawtrs.getInnermost();
        this.parallelInnermost = rawtrs.getParellelInnermost();
        this.outermost = rawtrs.getOutermost();
        this.minimal = rawtrs.getMinimal();
        this.setAssociativeFunctionSymbols(rawtrs.getAssociativeFunctionSymbols());
        this.setCommutativeFunctionSymbols(rawtrs.getCommutativeFunctionSymbols());
        this.setAssAndComFunctionSymbols(rawtrs.getAssAndCommFunctionSymbols());
        this.setPredefinedFunctionSemantics(rawtrs.getPredefinedFunctionSemantics());
        this.setDomainSemantics(rawtrs.getDomainSemantics());
        this.edges = rawtrs.getEdges();
        this.lhsVariableRelRules = rawtrs.getAllLHSVariableRules();
    }

    private QDependencyGraph getDPGraph(final QTRSProblem rWithQ) {
        final Set<Node<Rule>> nodes = new LinkedHashSet<Node<Rule>>();
        for (final Rule pair : this.pairs) {
            nodes.add(new Node<Rule>(pair));
        }
        final ArrayList<Node<Rule>> lookup = new ArrayList<Node<Rule>>(nodes);
        final Set<Edge<Void, Rule>> edges = new LinkedHashSet<Edge<Void, Rule>>();
        for (final Map.Entry<Integer, Integer> p : this.edges) {
            final int from = p.getKey() - 1;
            final int to = p.getValue() - 1;
            edges.add(new Edge<Void, Rule>(lookup.get(from), lookup.get(to)));
        }
        final Graph<Rule, Void> graph = new Graph<Rule, Void>(nodes, edges);
        return QDependencyGraph.create(graph, rWithQ);
    }

    private QTRSProblem getQTRS() {
        if (this.qFunctionApplications == null) {
            return QTRSProblem.create(ImmutableCreator.create(this.simpleRules));
        }
        return QTRSProblem.create(ImmutableCreator.create(this.simpleRules), this.qFunctionApplications);
    }

    private void setAssAndComFunctionSymbols(Set<String> assAndCommFunctionSymbols) {
        if (ObligationCreator.notEmpty(assAndCommFunctionSymbols)) {
            this.assAndComFunctionSymbols = new TreeSet<String>();
            this.assAndComFunctionSymbols.addAll(assAndCommFunctionSymbols);
        } else {
            assAndCommFunctionSymbols = null;
        }
    }

    private void setAssociativeFunctionSymbols(final Set<String> associativeFunctionSymbols) {
        if (ObligationCreator.notEmpty(associativeFunctionSymbols)) {
            this.associativeFunctionSymbols = new TreeSet<String>();
            this.associativeFunctionSymbols.addAll(associativeFunctionSymbols);
        } else {
            this.associativeFunctionSymbols = null;
        }
    }

    private void setCommutativeFunctionSymbols(final Set<String> commutativeFunctionSymbols) {
        if (ObligationCreator.notEmpty(commutativeFunctionSymbols)) {
            this.commutativeFunctionSymbols = new TreeSet<String>();
            this.commutativeFunctionSymbols.addAll(commutativeFunctionSymbols);
        } else {
            this.commutativeFunctionSymbols = null;
        }
    }

    private void setDomainSemantics(final Map<FunctionSymbol, Domain> domainSemantics) {
        if (domainSemantics == null || domainSemantics.isEmpty()) {
            this.domainSemantics = null;
        } else {
            this.domainSemantics = domainSemantics;
        }
    }

    private void setPredefinedFunctionSemantics(
        final Map<FunctionSymbol, PredefinedFunction<? extends Domain>> predefinedFunctionSemantics
    ) {
        if (predefinedFunctionSemantics == null || predefinedFunctionSemantics.isEmpty()) {
            this.predefinedFunctionSemantics = null;
        } else {
            this.predefinedFunctionSemantics = predefinedFunctionSemantics;
        }
    }

}
