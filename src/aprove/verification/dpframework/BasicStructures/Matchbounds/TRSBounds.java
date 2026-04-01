package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBoundsHelper.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.TreeAutomaton.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class TRSBounds {

    public enum Bound {
        MATCH, ROOF, MATCHRAISE, ROOFRAISE, MATCHDP, TOPDP, MATCHRAISEDP, TOPRAISEDP, MATCHRT, MATCHRAISERT
    };

    private boolean isRaiseBound(final Bound bound) {
        if (bound == Bound.MATCHRAISE || bound == Bound.ROOFRAISE || bound == Bound.TOPRAISEDP || bound == Bound.MATCHRAISEDP
                        || bound == Bound.MATCHRAISERT) {
            return true;
        }

        return false;
    }

    private boolean isDpBound(final Bound bound) {
        if (bound == Bound.MATCHDP || bound == Bound.TOPDP || bound == Bound.MATCHRAISEDP || bound == Bound.TOPRAISEDP) {
            return true;
        }

        return false;
    }

    /*
     * Strategy for the Tree Automaton to start with
     */
    public static enum STAStrategy {
        OOS, //use only one state
        OSFEFS, //one state or every function symbol,
        RC_SPLIT, RC_DEFSPLIT, // used to show runtime coplexity
        DP_SPLIT, DP_DEFSPLIT // used for DP problems

    };

    /*
     * Strategy to resolve conflicts
     */
    public static enum ConflictResolvingStrategy {
        NSFEPS, //introduce a new state for every proper subterm
        KMS, // use the strategy described in the paper "Match-Bounds Revisited" by Korp and Middeldorp
        MYCRS,
        // used for testing
        MYCRS2
    };

    public static enum WhenToBuildTAStrategy {
        BUILD_TA_AFTER_RESOLVING_ONE_CONFLICT, BUILD_TA_AFTER_RESOLVING_ALL_CONFLICTS
    };

    public static enum QuasiDetStrategy {
        EXACT,
        APPROX
    };

    public class Certificate {
        private final Bound bound;
        private final int boundedBy;
        private final Set<Integer> finalStatesForProof;
        private final TreeAutomaton<FunctionSymbol, Integer> compTA;
        private final ImmutableMap<FunctionSymbol, AnnotatedFunctionSymbol> fSMapper;

        public Certificate(final Bound bound, final int boundedBy, final Set<Integer> finalStatesForProof, final TreeAutomaton<FunctionSymbol, Integer> treeAutomaton,
                        final ImmutableMap<FunctionSymbol, AnnotatedFunctionSymbol> fSMapper) {
            this.bound = bound;
            this.boundedBy = boundedBy;

            /*
             * These are the final states needed to prove L(Sigma_0) <= L(A) for a tree automaton A.
             * Note that this information is actually not really needed to prove L(Sigma_0) <= L(A) but CeTA uses
             * it as they don't use a decision procedure to decide L(Sigma_0) <= L(A) but rather a sufficient criterion.
             */
            this.finalStatesForProof = finalStatesForProof;
            this.compTA = treeAutomaton;
            this.fSMapper = fSMapper;
        }

        public Bound getBound() {
            return this.bound;
        }

        public int getBoundedBy() {
            return this.boundedBy;
        }

        public Set<Integer> getFinalStates() {
            return this.finalStatesForProof;
        }

        public TreeAutomaton<FunctionSymbol, Integer> getTreeAutomaton() {
            return this.compTA;
        }

        public ImmutableMap<FunctionSymbol, AnnotatedFunctionSymbol> getFSMapper() {
            return this.fSMapper;
        }

        public void printTA(final Export_Util o, final StringBuilder result) {
            result.append("final states : " + this.getTreeAutomaton().getFinalStates());
            result.append(o.linebreak());
            result.append("transitions: ");
            result.append(o.linebreak());
            for (final Transition<FunctionSymbol, Integer> trans : this.getTreeAutomaton().getTransitions()) {
                final AnnotatedFunctionSymbol base = this.getFSMapper().get(trans.getLhsFunctionSymbol());
                result.append(base.f.getName() + base.nr + "(");
                final int numberOfStateParams = trans.getLhsStateParameters().size();
                int index = 1;
                for (final Integer state : trans.getLhsStateParameters()) {
                    if (index < numberOfStateParams) {
                        result.append(state + ", ");
                        index++;
                    } else {
                        result.append(state.toString());
                    }
                }
                result.append(")" + " " + o.rightarrow() + " " + trans.getRhsState());
                result.append(o.linebreak());
            }
            for (final Map.Entry<Integer, Set<Integer>> entry : this.getTreeAutomaton().getEpsTransitions().entrySet()) {
                final Integer lhs = entry.getKey();
                for (final Integer rhs : entry.getValue()) {
                    result.append(lhs + " " + o.rightarrow() + " " + rhs);
                    result.append(o.linebreak());
                }

            }
        }

        public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
            final Element boundProofTag = CPFTag.BOUNDS.createElement(doc);

            final Element boundTag = CPFTag.TYPE.createElement(doc);
            if (this.bound == TRSBounds.Bound.MATCH || this.bound == TRSBounds.Bound.MATCHRAISE) {
                boundTag.appendChild(CPFTag.MATCH.createElement(doc));
            } else if (this.bound == TRSBounds.Bound.ROOF) {
                boundTag.appendChild(CPFTag.ROOF.createElement(doc));
            } else {
                assert (false) : "No bound type set!!!";
            }
            boundProofTag.appendChild(boundTag);

            final Element boundElement = CPFTag.BOUND.createElement(doc);
            boundElement.appendChild(doc.createTextNode("" + this.getBoundedBy()));
            boundProofTag.appendChild(boundElement);

            final Element finalStatesTag = CPFTag.FINAL_STATES.createElement(doc);
            for (final Integer state : this.finalStatesForProof) {
                final Element stateTag = CPFTag.STATE.createElement(doc);
                stateTag.appendChild(doc.createTextNode(state.toString()));
                finalStatesTag.appendChild(stateTag);
            }
            boundProofTag.appendChild(finalStatesTag);
            final Element treeAutomatonTag = CPFTag.TREE_AUTOMATON.createElement(doc);
            final Element finalStatesTagCopy = CPFTag.FINAL_STATES.createElement(doc);
            final Set<Integer> allFinStates = new HashSet<>(this.compTA.getFinalStates());
            allFinStates.addAll(this.finalStatesForProof);
            for (final Integer state : allFinStates) {
                final Element stateTag = CPFTag.STATE.createElement(doc);
                stateTag.appendChild(doc.createTextNode(state.toString()));
                finalStatesTagCopy.appendChild(stateTag);
            }
            treeAutomatonTag.appendChild(finalStatesTagCopy);

            final Map<FunctionSymbol, AnnotatedFunctionSymbol> symbolToAnnotatedMap = this.getFSMapper();
            final Element transitions = CPFTag.TRANSITIONS.createElement(doc);
            for (final Transition<FunctionSymbol, Integer> transition : this
                .getTreeAutomaton()
                .getTransitions())
            {
                final Element transitionTag = CPFTag.TRANSITION.createElement(doc);
                final FunctionSymbol symbol = transition.getLhsFunctionSymbol();
                final AnnotatedFunctionSymbol annotatedSymbol = symbolToAnnotatedMap.get(symbol);
                final Element transitionLhs = CPFTag.LHS.createElement(doc);
                transitionLhs.appendChild(annotatedSymbol.f.toCPF(doc, xmlMetaData));
                final Element height = CPFTag.HEIGHT.createElement(doc);
                height.appendChild(doc.createTextNode("" + annotatedSymbol.nr));
                transitionLhs.appendChild(height);
                for (final Integer s : transition.getLhsStateParameters()) {
                    final Element stateLhs = CPFTag.STATE.createElement(doc);
                    stateLhs.appendChild(doc.createTextNode("" + s));
                    transitionLhs.appendChild(stateLhs);
                }
                transitionTag.appendChild(transitionLhs);

                final Element transitionRhs = CPFTag.RHS.createElement(doc);
                final Element stateRhs = CPFTag.STATE.createElement(doc);
                stateRhs.appendChild(doc.createTextNode("" + transition.getRhsState()));
                transitionRhs.appendChild(stateRhs);
                transitionTag.appendChild(transitionRhs);

                transitions.appendChild(transitionTag);
            }
            // epsilon transitions
            for (final Map.Entry<Integer, Set<Integer>> epsTrans : this
                .getTreeAutomaton()
                .getEpsTransitions()
                .entrySet())
            {
                final Integer lhsStateInteger = epsTrans.getKey();
                for (final Integer rhs : epsTrans.getValue()) {
                    final Element transitionTag = CPFTag.TRANSITION.createElement(doc);

                    final Element transitionLhs = CPFTag.LHS.createElement(doc);
                    final Element stateLhs = CPFTag.STATE.createElement(doc);
                    stateLhs.appendChild(doc.createTextNode("" + lhsStateInteger));
                    transitionLhs.appendChild(stateLhs);

                    final Element transitionRhs = CPFTag.RHS.createElement(doc);
                    final Element stateRhs = CPFTag.STATE.createElement(doc);
                    stateRhs.appendChild(doc.createTextNode("" + rhs));
                    transitionRhs.appendChild(stateRhs);

                    transitionTag.appendChild(transitionLhs);
                    transitionTag.appendChild(transitionRhs);

                    transitions.appendChild(transitionTag);
                }
            }
            treeAutomatonTag.appendChild(transitions);
            boundProofTag.appendChild(treeAutomatonTag);
            return boundProofTag;
        }

    }

    private final Bound bound;
    private EnrichmentBuilder enrichment;
    private Set<Rule> romR; // contains the annotated TRS over signatureOfTA corresponding to the bound
    private Set<FunctionSymbol> signatureOfTA; // holds the signature of the current TA
    private Set<Rule> R; // contains original TRS R
    private final STAStrategy sTAS;
    private final ConflictResolvingStrategy cRS;
    private int boundedBy = 0;
    private int nextNewState = 0; // Shows which int can be used as a absolutely new State in a TA; after using it, nextNewState is increased by 1
    private final Set<Integer> finalStatesForProof; // used to create the certificate. See comment in class TRSBounds.Certificate.
    private boolean runtimeComplexity = false;
    private boolean useRFC = false;

    private Set<FunctionSymbol> definedSymbols = null; // used for runtime complexity


    private TRSBoundsTA.BijectiveStateToPowStateMapper sTPS = null;

    private final WhenToBuildTAStrategy wTBTA;
    private QuasiDetStrategy qDS;

    final int MAX_CONFLICTS_TO_RESOLVE;
    final int MAX_TRANSITIONS_OF_A;
    final int MAX_STATES_OF_A;

    private ConflictResolver confResolver;
    private final Map<Pair<TRSTerm, StateSubstitution<Integer>>, Set<Integer>> alreadyFoundConflicts;

    private TRSBounds(final Bound bound, final STAStrategy sTAS, final ConflictResolvingStrategy cRS, final WhenToBuildTAStrategy wTBTA, final int maxConflictsToResolve,
                    final int maxTransitions, final int maxStates) {

        this.bound = bound;
        this.sTAS = sTAS;
        this.cRS = cRS;

        this.wTBTA = wTBTA;

        this.MAX_CONFLICTS_TO_RESOLVE = maxConflictsToResolve;
        this.MAX_TRANSITIONS_OF_A = maxTransitions;
        this.MAX_STATES_OF_A = maxStates;

        this.finalStatesForProof = new LinkedHashSet<Integer>();
        this.alreadyFoundConflicts = new LinkedHashMap<Pair<TRSTerm, StateSubstitution<Integer>>, Set<Integer>>();
    }

    public TRSBounds(final Set<Rule> R, final Bound bound, final STAStrategy sTAS, final ConflictResolvingStrategy cRS, final WhenToBuildTAStrategy wTBTA,
                     final int maxConflictsToResolve, final int maxTransitions, final int maxStates, final boolean useRFC) {
        this(bound, sTAS, cRS, wTBTA, maxConflictsToResolve, maxTransitions, maxStates);
        if (Globals.useAssertions) {
            assert (R != null);
            assert (bound == Bound.MATCH || bound == Bound.ROOF);
            assert (sTAS != null);
        }

        this.useRFC = useRFC;
        this.init(R);
        this.confResolver = new ConflictResolver(this.nextNewState, null, this.enrichment.getFuncSymbGen());
    }

    public TRSBounds(final Set<Rule> R, final Bound bound, final STAStrategy sTAS, final ConflictResolvingStrategy cRS, final WhenToBuildTAStrategy wTBTA, final QuasiDetStrategy qDS,
                     final int maxConflictsToResolve, final int maxTransitions, final int maxStates, final boolean useRFC) {
        this(bound, sTAS, cRS, wTBTA, maxConflictsToResolve, maxTransitions, maxStates);
        if (Globals.useAssertions) {
            assert (bound == Bound.MATCHRAISE || bound == Bound.ROOFRAISE);
        }
        this.init(R);
        this.sTPS = new TRSBoundsTA.BijectiveStateToPowStateMapper();
        this.qDS = qDS;
        this.useRFC = useRFC;
        this.confResolver = new ConflictResolver(this.nextNewState, this.sTPS, this.enrichment.getFuncSymbGen());
    }

    public TRSBounds(final Set<Rule> R, final Set<Rule> P, final Rule ruleToDelete, final Bound bound, final STAStrategy sTAS, final ConflictResolvingStrategy cRS,
                     final WhenToBuildTAStrategy wTBTA, final int maxConflictsToResolve, final int maxTransitions, final int maxStates, final boolean useRFC) {
        this(bound, sTAS, cRS, wTBTA, maxConflictsToResolve, maxTransitions, maxStates);
        if (Globals.useAssertions) {
            assert (bound == Bound.MATCHDP || bound == Bound.TOPDP);
            assert (P.contains(ruleToDelete));
        }

        this.init(R, P, ruleToDelete);
        if (this.sTAS == STAStrategy.DP_SPLIT) {
            this.definedSymbols = new LinkedHashSet<FunctionSymbol>();
            for (final Rule p : P) {
                this.definedSymbols.add(p.getRootSymbol());
            }
        }
        this.useRFC = useRFC;
        this.confResolver = new ConflictResolver(this.nextNewState, null, this.enrichment.getFuncSymbGen());
    }

    public TRSBounds(final Set<Rule> R, final Set<Rule> P, final Rule ruleToDelete, final Bound bound, final STAStrategy sTAS, final ConflictResolvingStrategy cRS,
                     final WhenToBuildTAStrategy wTBTA, final QuasiDetStrategy qDS, final int maxConflictsToResolve, final int maxTransitions, final int maxStates, final boolean useRFC) {
        this(bound, sTAS, cRS, wTBTA, maxConflictsToResolve, maxTransitions, maxStates);
        if (Globals.useAssertions) {
            assert (bound == Bound.MATCHRAISEDP || bound == Bound.TOPRAISEDP);
            assert (P.contains(ruleToDelete));
        }
        this.init(R, P, ruleToDelete);
        this.sTPS = new TRSBoundsTA.BijectiveStateToPowStateMapper();
        this.qDS = qDS;
        if (this.sTAS == STAStrategy.DP_SPLIT) {
            this.definedSymbols = new LinkedHashSet<FunctionSymbol>();
            for (final Rule p : P) {
                this.definedSymbols.add(p.getRootSymbol());
            }
        }
        this.useRFC = useRFC;
        this.confResolver = new ConflictResolver(this.nextNewState, this.sTPS, this.enrichment.getFuncSymbGen());
    }

    public TRSBounds(final RuntimeComplexityTrsProblem cpxTrs,  final Bound bound, final STAStrategy sTAS, final ConflictResolvingStrategy cRS, final WhenToBuildTAStrategy wTBTA, final QuasiDetStrategy qDS,
                    final int maxConflictsToResolve, final int maxTransitions, final int maxStates) {
        this(bound, sTAS, cRS, wTBTA, maxConflictsToResolve, maxTransitions, maxStates);
        this.init(cpxTrs.getR());
        this.definedSymbols = cpxTrs.getDefinedSymbols();
        this.sTPS = new TRSBoundsTA.BijectiveStateToPowStateMapper();
        this.qDS = qDS;
        this.runtimeComplexity = true;
        this.confResolver = new ConflictResolver(this.nextNewState, this.sTPS, this.enrichment.getFuncSymbGen());
    }

    public TRSBounds(final CdtProblem cdtProblem, final Cdt ruleToDelete, final Bound bound, final STAStrategy sTAS, final ConflictResolvingStrategy cRS,
                     final WhenToBuildTAStrategy wTBTA, final QuasiDetStrategy qDS, final int maxConflictsToResolve, final int maxTransitions, final int maxStates) {
        this(bound, sTAS, cRS, wTBTA, maxConflictsToResolve, maxTransitions, maxStates);
        if (Globals.useAssertions) {
            assert (bound == Bound.MATCHRT || bound == Bound.MATCHRAISERT);
            assert (cdtProblem.getTuples().contains(ruleToDelete));
        }
        this.init(cdtProblem, ruleToDelete);
        this.definedSymbols = cdtProblem.getDefinedPSymbols();
        this.sTPS = new TRSBoundsTA.BijectiveStateToPowStateMapper();
        this.qDS = qDS;
        this.runtimeComplexity = true;
        this.confResolver = new ConflictResolver(this.nextNewState, this.sTPS, this.enrichment.getFuncSymbGen());
    }

    private void init(final CdtProblem cdtProblem, final Cdt ruleToDelete) {
        this.R = cdtProblem.getR();
        final Set<Rule> PWithoutRuleToRemove = new LinkedHashSet<Rule>();
        for (final Cdt cdt : cdtProblem.getTuples()) {
            if (!cdt.equals(ruleToDelete)) {
                PWithoutRuleToRemove.add(cdt.getRule());
            }
        }

        final Rule ruleToRemove = ruleToDelete.getRule();

        this.enrichment = new RTEnrichmentBuilder(this.bound, this.R, PWithoutRuleToRemove, ruleToRemove);

        this.signatureOfTA = new LinkedHashSet<FunctionSymbol>();
        for (final Rule r : this.R) {
            for (final FunctionSymbol f : r.getFunctionSymbols()) {
                this.signatureOfTA.add(this.enrichment.lift(f, 0));
            }
        }
        for (final Rule r : PWithoutRuleToRemove) {
            for (final FunctionSymbol f : r.getFunctionSymbols()) {
                this.signatureOfTA.add(this.enrichment.lift(f, 0));
            }
        }
        for (final FunctionSymbol f : ruleToRemove.getFunctionSymbols()) {
            this.signatureOfTA.add(this.enrichment.lift(f, 0));
        }
        this.romR = this.enrichment.getTRS();
    }


    /*
     * Inits everything that has to do with the DP-Problem (R, P) and the Rule to delete
     */
    private void init(final Set<Rule> R, final Set<Rule> P, final Rule ruleToDelete) {
        this.R = R;
        final Set<Rule> PWithoutRuleToRemove = new LinkedHashSet<Rule>(P);
        PWithoutRuleToRemove.remove(ruleToDelete);
        final Rule ruleToRemove = ruleToDelete;

        this.enrichment = new DPEnrichmentBuilder(this.bound, R, PWithoutRuleToRemove, ruleToRemove);

        this.signatureOfTA = new LinkedHashSet<FunctionSymbol>();
        for (final Rule r : R) {
            for (final FunctionSymbol f : r.getFunctionSymbols()) {
                this.signatureOfTA.add(this.enrichment.lift(f, 0));
            }
        }
        for (final Rule r : PWithoutRuleToRemove) {
            for (final FunctionSymbol f : r.getFunctionSymbols()) {
                this.signatureOfTA.add(this.enrichment.lift(f, 0));
            }
        }
        for (final FunctionSymbol f : ruleToRemove.getFunctionSymbols()) {
            this.signatureOfTA.add(this.enrichment.lift(f, 0));
        }
        this.romR = this.enrichment.getTRS();
    }

    /*
     *  Inits everything that has to do with the TRS R-
     */
    private void init(final Set<Rule> R) {
        this.R = R;
        this.enrichment = new TRSEnrichmentBuilder(this.bound, this.R);
        this.signatureOfTA = new LinkedHashSet<FunctionSymbol>();
        for (final Rule r : R) {
            for (final FunctionSymbol f : r.getFunctionSymbols()) {
                this.signatureOfTA.add(this.enrichment.lift(f, 0));
            }
        }
        this.romR = this.enrichment.getTRS();
    }

    /*
     * Trys to prove the type of boundedness which is specified by the member variable bound.
     * If boundedness could not be proven it returns null; otherwise it returns a certificate
     * consisting of the information which is needed for a proof.
     */
    public Certificate getCertificate(final Abortion aborter) throws AbortionException {
        final boolean isNotRaiseBound = !this.isRaiseBound(this.bound);

        TreeAutomaton<FunctionSymbol, Integer> startingA = null;
        Set<Integer> finalStatesForCPF = null;

        // Set start automaton
        if (this.useRFC) {
            ConflictResolver confResForRFC;


            if (this.isDpBound(this.bound)) {
                final DPEnrichmentBuilder dpEnrichment = (DPEnrichmentBuilder) this.enrichment;

                final Set<Rule> rulesForTRSBuilder = new LinkedHashSet<Rule>();
                // We have to consider (R union P)#' as a TRS to which we want to reach compatibility
                rulesForTRSBuilder.addAll(this.R);
                rulesForTRSBuilder.addAll(dpEnrichment.getPWithoutRuleToRemove());
                rulesForTRSBuilder.add(dpEnrichment.getRuleToRemove());
                final TRSBuilderForRFC trsBuilderForRFC = new TRSBuilderForRFC(rulesForTRSBuilder);
                confResForRFC = new ConflictResolver(this.nextNewState, this.sTPS, trsBuilderForRFC.funcSymbGen);
                final Set<Rule> sharpedTRS = trsBuilderForRFC.getSharpedTRS(aborter);
                final TRSFunctionApplication sharpConst = trsBuilderForRFC.getSharpConst();

                // For DP-Problems, it is enough to consider RFC(t sigma#), where s->t is the rule we want to remove
                final Set<Rule> singleRuleSet = new LinkedHashSet<Rule>();
                singleRuleSet.add(dpEnrichment.getRuleToRemove());
                startingA = this.getStartingTAForRFC(singleRuleSet, sharpConst, confResForRFC, aborter);
                startingA = this.createCompatibleTAForRFC(startingA, sharpedTRS, confResForRFC, aborter);
            } else {
                final TRSBuilderForRFC trsBuilderForRFC = new TRSBuilderForRFC(this.R);
                final Set<Rule> sharpedTRS = trsBuilderForRFC.getSharpedTRS(aborter);
                final TRSFunctionApplication sharpConst = trsBuilderForRFC.getSharpConst();
                confResForRFC = new ConflictResolver(this.nextNewState, this.sTPS, trsBuilderForRFC.funcSymbGen);
                startingA = this.getStartingTAForRFC(this.R, sharpConst, confResForRFC, aborter);
                startingA = this.createCompatibleTAForRFC(startingA, sharpedTRS, confResForRFC, aborter);
            }

            for (final Map.Entry<TRSTerm, Integer> entry : confResForRFC.getStateMap().entrySet()) {
                this.confResolver.putToStateMap(this.enrichment.lift(entry.getKey(), 0), entry.getValue());
            }
            startingA = this.lift(startingA, 0);
        } else {
            final Pair<TreeAutomaton<FunctionSymbol, Integer>, Set<Integer>> A_fin = this.getStartAutomaton();
            startingA = A_fin.x;
            finalStatesForCPF = A_fin.y;
        }

        this.confResolver.setNextNewState(this.nextNewState);

        if (isNotRaiseBound) {
            final TreeAutomaton<FunctionSymbol, Integer> A = this.createCompatibleTA(startingA, aborter);

            if (A != null) {
                if (finalStatesForCPF == null) {
                    finalStatesForCPF = this.finalStatesForProof;
                }
                return new Certificate(this.bound, this.boundedBy, finalStatesForCPF, A, this.enrichment.fSMapper.getfSToAFS());
            } else {
                return null;
            }

        } else {
            final TRSBoundsTA.QuasiDeterministicTA A = this.createQDRCQCompatibleTA(startingA, aborter);

            if (A != null) {
                if (finalStatesForCPF == null) {
                    finalStatesForCPF = this.finalStatesForProof;
                }
                return new Certificate(
                    this.bound,
                    this.boundedBy,
                    finalStatesForCPF,
                    A.getDetAutomaton(),
                    this.enrichment.fSMapper.getfSToAFS());
            } else {
                return null;
            }
        }
    }

    private TreeAutomaton<FunctionSymbol, Integer> lift(final TreeAutomaton<FunctionSymbol, Integer> A, final int height) {
        final Set<Transition<FunctionSymbol, Integer>> newTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
        for (final Transition<FunctionSymbol, Integer> trans : A.getTransitions()) {
            final FunctionSymbol newF = this.enrichment.lift(trans.getLhsFunctionSymbol(), height);
            newTransitions.add(Transition.create(newF, trans.getLhsStateParameters(), trans.getRhsState()));
        }

        return TreeAutomaton.create(A.getFinalStates(), A.getTransitions(), A.getEpsTransitions());
    }

    private TreeAutomaton<FunctionSymbol, Integer> getStartingTAForRFC(final Set<Rule> R, final TRSFunctionApplication sharpedConst,
                    final ConflictResolver confRes, final Abortion aborter)
                    throws AbortionException {
        TreeAutomaton<FunctionSymbol, Integer> A = TreeAutomaton.createEmpty();
        for (final Rule r : R) {
            aborter.checkAbortion();
            final TRSTerm rhs = r.getRight();

            final Map<TRSVariable, TRSTerm> subs = new LinkedHashMap<TRSVariable, TRSTerm>();
            for (final TRSVariable x : r.getVariables()) {
                subs.put(x, sharpedConst);
            }

            final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(subs));
            final TRSTerm startingTerm = rhs.applySubstitution(sigma);


            final Conflict conf = new Conflict(startingTerm, StateSubstitution.<Integer> createEmpty(), this.nextNewState, r);
            final Set<Integer> newFinalStates = new LinkedHashSet<Integer>();
            newFinalStates.add(this.nextNewState);

            if (this.isRaiseBound(this.bound)) {
                final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                initSTPS.add(this.nextNewState);
                this.sTPS.set(this.nextNewState, initSTPS);
            }

            final Integer newNextStateForConfRes = this.nextNewState + 1;
            confRes.setNextNewState(newNextStateForConfRes);
            final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResConflict = confRes.resolveConflict(A, conf, aborter);

            this.nextNewState = confRes.getNextNewState();
            A = this.union(A, newFinalStates, transToResConflict.x, transToResConflict.y);
        }

        return A;
    }

    private TreeAutomaton<FunctionSymbol, Integer> union(final TreeAutomaton<FunctionSymbol, Integer> A, final Set<Integer> finalStates,
                    final Set<Transition<FunctionSymbol, Integer>> resolvingTransitions, final Map<Integer, Set<Integer>> epsTrans) {
        Set<Transition<FunctionSymbol, Integer>> oldTransitions;
        Set<Transition<FunctionSymbol, Integer>> transForNewTA = null;
        Set<Integer> finalStatesForNewTA = null;
        Map<Integer, Set<Integer>> epsTransForNewTA = null;

        oldTransitions = A.getTransitions();
        transForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>(oldTransitions);
        transForNewTA.addAll(resolvingTransitions);
        finalStatesForNewTA = new LinkedHashSet<Integer>(A.getFinalStates());
        finalStatesForNewTA.addAll(finalStates);

        epsTransForNewTA = TreeAutomatonHelper.unionEpsTransitions(A.getEpsTransitions(), epsTrans);
        return TreeAutomaton.<FunctionSymbol, Integer> create(finalStatesForNewTA, transForNewTA, epsTransForNewTA);
    }

    private TreeAutomaton<FunctionSymbol, Integer> createCompatibleTAForRFC(final TreeAutomaton<FunctionSymbol, Integer> startingA, final Set<Rule> sharpedTRS,
                    final ConflictResolver confRes, final Abortion aborter)
                    throws AbortionException {
        aborter.checkAbortion();
        TreeAutomaton<FunctionSymbol, Integer> A = startingA;
        int debugI = 0;
        if (Globals.DEBUG_MARCEL) {
            Logger.getAnonymousLogger().severe("AForRFC" + debugI + ": " + A);
            debugI++;
        }
        boolean aIsCompatible = false;
        int conflictsResolved = 0;
        aborter.checkAbortion();

        while (!aIsCompatible) {
            aborter.checkAbortion();
            final Set<Conflict> conflicts = this.collectAllCompatibleConflicts(A, sharpedTRS, aborter);

            if (Globals.DEBUG_MARCEL) {
                Logger.getAnonymousLogger().severe("Conflicts: " + conflicts);
            }

            if (conflicts.isEmpty()) {
                aIsCompatible = true;
                this.nextNewState = confRes.getNextNewState();
            } else {
                conflictsResolved += conflicts.size();
                if (conflictsResolved > this.MAX_CONFLICTS_TO_RESOLVE) {
                    A = null;
                    break;
                }

                for (final Conflict conf : conflicts) {
                    final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResConflict = confRes.resolveConflict(A, conf,
                        aborter);
                    A = this.union(A, new LinkedHashSet<Integer>(), transToResConflict.x, transToResConflict.y);
                }

                if (A.getAllStates().size() > this.MAX_STATES_OF_A
                                || A.getTransitions().size() + A.getEpsTransitions().size() > this.MAX_TRANSITIONS_OF_A) {

                    A = null;
                    break;
                }

                if (Globals.DEBUG_MARCEL) {
                    Logger.getAnonymousLogger().severe("AForRFC" + debugI + ": " + A);
                    debugI++;
                }
            }

        }

        return A;
    }

    /*
     * Trys to create a compatible TreeAutomaton for romR.
     * Updates romR and boundedBy if needed.
     */
    private TreeAutomaton<FunctionSymbol, Integer> createCompatibleTA(final TreeAutomaton<FunctionSymbol, Integer> startingA, final Abortion aborter)
                    throws AbortionException {
        aborter.checkAbortion();
        TreeAutomaton<FunctionSymbol, Integer> A = startingA;

        for (final int state : A.getFinalStates()) {
            this.finalStatesForProof.add(state);
        }

        int debugI = 0;
        if (Globals.DEBUG_MARCEL) {
            Logger.getAnonymousLogger().severe("A" + debugI + ": " + A);
            debugI++;
        }

        boolean aIsCompatible = false;
        int conflictsResolved = 0;
        aborter.checkAbortion();

        while (!aIsCompatible) {

            final Set<Conflict> conflicts = this.collectAllCompatibleConflicts(A, this.enrichment.getTRS(), aborter);

            if (Globals.DEBUG_MARCEL) {
                Logger.getAnonymousLogger().severe("romR: " + this.romR);
                Logger.getAnonymousLogger().severe("Conflicts: " + conflicts);
            }

            if (conflicts.isEmpty()) {
                aIsCompatible = true;
            } else {
                conflictsResolved += conflicts.size();
                if (conflictsResolved > this.MAX_CONFLICTS_TO_RESOLVE) {
                    A = null;
                    break;
                }

                A = this.resolveConflictsAndExtendSignatureOfTA(A, conflicts, aborter);

                if (A.getAllStates().size() > this.MAX_STATES_OF_A
                    || A.getTransitions().size() + A.getEpsTransitions().size() > this.MAX_TRANSITIONS_OF_A) {

                    A = null;
                    break;
                }

                aborter.checkAbortion();
                this.updateRomRAndBound(aborter);
                aborter.checkAbortion();

                if (Globals.DEBUG_MARCEL) {
                    Logger.getAnonymousLogger().severe("A" + debugI + ": " + A);
                    debugI++;
                }
            }

        }
        if (Globals.DEBUG_MARCEL) {
            Logger.getAnonymousLogger().severe("Bound: " + this.boundedBy);
        }
        return A;

    }

    private TRSBoundsTA.QuasiDeterministicTA createQDRCQCompatibleTA(final TreeAutomaton<FunctionSymbol, Integer> startingA, final Abortion aborter)
                    throws AbortionException {
        TreeAutomaton<FunctionSymbol, Integer> A = startingA;
        TRSBoundsTA.QuasiDeterministicTA qDetA;

        this.signatureOfTA = new LinkedHashSet<FunctionSymbol>(A.getAllFunctionSymbols());

        if (this.qDS == QuasiDetStrategy.APPROX) {
            qDetA = this.makeAgainQDaRCWithApproxStrat(A);
        } else /* qDS == QuasiDetStrategy.EXACT */{
            qDetA = this.makeAgainQDaRC(A);
        }

        this.confResolver.setNextNewState(this.nextNewState);

        int debugI = 0;
        final Logger log = Logger.getLogger("");
        if (Globals.DEBUG_MARCEL) {
            log.severe("qDetA" + debugI + ": " + qDetA);
        }

        boolean aIsQDRCQCompatible = false;
        int conflictsResolved = 0;

        while (!aIsQDRCQCompatible) {

            final Set<Conflict> conflicts = this.collectAllQCompatibleConflicts(qDetA, aborter);

            aborter.checkAbortion();

            if (Globals.DEBUG_MARCEL) {
                log.severe("Conflicts: " + conflicts);
            }

            if (conflicts.isEmpty()) {
                aIsQDRCQCompatible = true;
            } else {

                A = this.resolveQCompConflictsAndExtendSignatureOfRomR(qDetA, conflicts, aborter);

                if (Globals.DEBUG_MARCEL) {
                    debugI++;
                    log.severe("A" + debugI + ": " + A);
                }

                conflictsResolved += conflicts.size();
                if (conflictsResolved > this.MAX_CONFLICTS_TO_RESOLVE) {
                    qDetA = null;
                    break;
                }

                if (Globals.DEBUG_MARCEL) {
                    log.severe("Conflicts: " + conflicts);
                }

                if (Globals.DEBUG_MARCEL) {
                    debugI++;
                    log.severe("A" + debugI + ": " + A);
                }

                if (this.qDS == QuasiDetStrategy.APPROX) {
                    qDetA = this.makeAgainQDaRCWithApproxStrat(A);
                } else /* qDS == QuasiDetStrategy.EXACT */{
                    qDetA = this.makeAgainQDaRC(A);
                }

                this.enrichment.setLhsSignature(qDetA.getAllFunctionSymbols());

                aborter.checkAbortion();
                this.updateRomRAndBound(aborter);
                aborter.checkAbortion();

                this.confResolver.setNextNewState(this.nextNewState);
                aborter.checkAbortion();

                if (qDetA.getTA().getAllStates().size() > this.MAX_STATES_OF_A
                                || qDetA.getTA().getTransitions().size() + qDetA.getTA().getEpsTransitions().size() > this.MAX_TRANSITIONS_OF_A) {

                    qDetA = null;
                    break;
                }

                if (Globals.DEBUG_MARCEL) {
                    log.severe("qDetA: " + qDetA + " ");
                }
                aborter.checkAbortion();
            }
        }

        if (Globals.DEBUG_MARCEL) {
            log.severe("Bound typ : " + (this.bound == Bound.MATCHRAISE ? "Match" : "Roof"));//Logger.getAnonymousLogger("Bound typ : " + (this.bound == Bound.MATCHRAISE ? "Match" : "Roof"));
            log.severe("Bound: " + this.boundedBy);
            log.severe("final: ");
            final Map<FunctionSymbol, Set<Transition<FunctionSymbol, Integer>>> map = new LinkedHashMap<FunctionSymbol, Set<Transition<FunctionSymbol, Integer>>>();
            for (final Transition<FunctionSymbol, Integer> trans : qDetA.getTransitions()) {
                final FunctionSymbol f = trans.getLhsFunctionSymbol();
                Set<Transition<FunctionSymbol, Integer>> transitions = map.get(f);
                if (transitions == null) {
                    transitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
                }
                transitions.add(trans);
                map.put(f, transitions);
            }
            for (final Map.Entry<FunctionSymbol, Set<Transition<FunctionSymbol, Integer>>> entry : map.entrySet()) {
                for (final Transition<FunctionSymbol, Integer> trans : entry.getValue()) {
                    boolean isDetTrans = false;
                    for (final Transition<FunctionSymbol, Integer> detTrans : qDetA.getDetTransitions()) {
                        if (trans.equals(detTrans)) {
                            isDetTrans = true;
                        }
                    }
                    log.severe(this.enrichment.base(trans.getLhsFunctionSymbol()).getName() + "_"
                                    + this.enrichment.height(trans.getLhsFunctionSymbol()) + "("
                        + trans.getLhsStateParameters()
                        + ") --> " + trans.getRhsState()
                        + (isDetTrans ? "*" : ""));
                }
            }
        }

        return qDetA;
    }

    private TRSBoundsTA.QuasiDeterministicTA makeAgainQDaRC(final TreeAutomaton<FunctionSymbol, Integer> A) {
        final TreeAutomaton<FunctionSymbol, Set<Integer>> powA = A.subsetConstructionWKT();
        final Set<Set<Integer>> powStates = powA.getAllStates();

        final Map<Integer, Set<Integer>> newEpsTransitions = new LinkedHashMap<Integer, Set<Integer>>(A.getEpsTransitions());
        final Map<Integer, Set<Integer>> detEpsTransitions = new LinkedHashMap<Integer, Set<Integer>>();

        /*
         * compute new quasi-det epsilon transitions
         */
        for (final Map.Entry<Integer, Set<Integer>> entry : A.getEpsTransitions().entrySet()) {
            final int lhsState = entry.getKey();
            final Set<Integer> qDetPowState = new LinkedHashSet<Integer>();
            for (final int state : A.getEpsTransitions().get(lhsState)) {
                qDetPowState.addAll(this.sTPS.getPowState(state));
            }

            this.updateSTPS(qDetPowState);
            powStates.add(qDetPowState);
            detEpsTransitions.put(lhsState, qDetPowState);
            final Set<Integer> newEpsReachableStates = new LinkedHashSet<Integer>(entry.getValue());
            newEpsReachableStates.add(this.sTPS.getState(qDetPowState));
            final Set<Integer> newQDetEpsState = new LinkedHashSet<Integer>();
            newQDetEpsState.add(this.sTPS.getState(qDetPowState));

            detEpsTransitions.put(lhsState, newQDetEpsState);
            newEpsTransitions.put(lhsState, newEpsReachableStates);
        }

        for (final Set<Integer> powState : powStates) {
            this.updateSTPS(powState);
        }

        final Set<Set<Integer>> powFinalStates = powA.getFinalStates();
        final Set<Integer> newFinalStates = new LinkedHashSet<Integer>();
        for (final Set<Integer> powFState : powFinalStates) {
            newFinalStates.add(this.sTPS.getState(powFState));
        }

        final Set<Transition<FunctionSymbol, Set<Integer>>> powTransitions = powA.getTransitions();
        final Set<Transition<FunctionSymbol, Integer>> newTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
        final Set<Transition<FunctionSymbol, Integer>> transitionsForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>(A.getTransitions());
        final Set<Transition<FunctionSymbol, Integer>> detTransitionsForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();

        for (final Transition<FunctionSymbol, Set<Integer>> powTrans : powTransitions) {
            final List<Set<Integer>> powStateParameters = powTrans.getLhsStateParameters();
            final List<Integer> newStateParameters = new ArrayList<Integer>();
            for (final Set<Integer> powStateParam : powStateParameters) {
                newStateParameters.add(this.sTPS.getState(powStateParam));
            }
            final int newRhsState = this.sTPS.getState(powTrans.getRhsState());
            final Transition<FunctionSymbol, Integer> newTrans = Transition.<FunctionSymbol, Integer> create(powTrans.getLhsFunctionSymbol(),
                newStateParameters, newRhsState);

            boolean desStateAlreadyThere = false;
            for (final Transition<FunctionSymbol, Integer> oldDetTrans : detTransitionsForNewTA) {
                final Set<Integer> newPowRhsState = this.sTPS.getPowState(newRhsState);
                final Set<Integer> oldPowRhsState = this.sTPS.getPowState(oldDetTrans.getRhsState());
                if (oldDetTrans.getLhsFunctionSymbol().equals(newTrans.getLhsFunctionSymbol())) {
                    if (oldDetTrans.getLhsStateParameters().equals(newTrans.getLhsStateParameters())) {
                        desStateAlreadyThere = true;
                        // if newPowRhsState is a superset of the old powRhsState then the new transition is used as a deterministic Transition
                        if (newPowRhsState.containsAll(oldPowRhsState)) {
                            detTransitionsForNewTA.remove(oldDetTrans);
                            detTransitionsForNewTA.add(newTrans);
                        }
                        break;
                    }
                }
            }

            if (!desStateAlreadyThere) {
                detTransitionsForNewTA.add(newTrans);
            }

            if (!A.getTransitions().contains(newTrans)) {
                newTransitions.add(newTrans);
            }

        }

        final Set<Transition<FunctionSymbol, Integer>> transForRC = this.computeTransForRC(transitionsForNewTA, newTransitions);
        transitionsForNewTA.addAll(transForRC);

        final TRSBoundsTA.QuasiDeterministicTA newA = TRSBoundsTA.QuasiDeterministicTA.create(newFinalStates, transitionsForNewTA, newEpsTransitions,
            detTransitionsForNewTA, detEpsTransitions);

        return newA;
    }

    private TRSBoundsTA.QuasiDeterministicTA makeAgainQDaRCWithApproxStrat(final TreeAutomaton<FunctionSymbol, Integer> A) {

        final Set<Set<Integer>> oldPowStates = new LinkedHashSet<Set<Integer>>();
        Set<Set<Integer>> newPowStates = new LinkedHashSet<Set<Integer>>();

        final Map<Integer, Set<Integer>> newEpsTransitions = new LinkedHashMap<Integer, Set<Integer>>(A.getEpsTransitions());
        final Map<Integer, Set<Integer>> detEpsTransitions = new LinkedHashMap<Integer, Set<Integer>>();

        /*
         * compute new quasi-det epsilon transitions
         */
        for (final Map.Entry<Integer, Set<Integer>> entry : A.getEpsTransitions().entrySet()) {
            final int lhsState = entry.getKey();
            final Set<Integer> qDetPowState = new LinkedHashSet<Integer>();
            for (final int state : A.getEpsTransitions().get(lhsState)) {
                qDetPowState.addAll(this.sTPS.getPowState(state));
                oldPowStates.add(this.sTPS.getPowState(state));
            }

            this.updateSTPS(qDetPowState);
            /*
             * We have to consider all det states as a new pow state (although they may already be known)
             * because we made A quasi-compatible before, i.e. we deleted for example a transition
             * f_0({1,2}, {1,2}) -> {1,2} although transitions like f_0(1,1) -> 1, f_0(1,1) -> 2 and
             * f_0(1,1) -> {1,2} exist yet
             */
            newPowStates.add(qDetPowState);

            detEpsTransitions.put(lhsState, qDetPowState);
            final Set<Integer> newEpsReachableStates = new LinkedHashSet<Integer>(entry.getValue());
            newEpsReachableStates.add(this.sTPS.getState(qDetPowState));
            final Set<Integer> newQDetEpsState = new LinkedHashSet<Integer>();
            newQDetEpsState.add(this.sTPS.getState(qDetPowState));

            detEpsTransitions.put(lhsState, newQDetEpsState);
            newEpsTransitions.put(lhsState, newEpsReachableStates);
        }

        final Map<Pair<FunctionSymbol, List<Integer>>, Set<Integer>> transitionsAsMap = new LinkedHashMap<Pair<FunctionSymbol, List<Integer>>, Set<Integer>>();
        final Map<Pair<FunctionSymbol, List<Integer>>, Set<Integer>> constTransitionsAsMap = new LinkedHashMap<Pair<FunctionSymbol, List<Integer>>, Set<Integer>>();
        final Set<Transition<FunctionSymbol, Integer>> posArEpsClosedTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();

        final Set<Transition<FunctionSymbol, Integer>> transitionsForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
        final Set<Transition<FunctionSymbol, Integer>> detTransitionsForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();

        final Set<Transition<FunctionSymbol, Integer>> newTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();

        /*
         * init
         */
        for (final Transition<FunctionSymbol, Integer> trans : A.getTransitions()) {
            final Integer rhsState = trans.getRhsState();
            final Set<Integer> epsTransClosStates = A.epsTransClosure(rhsState);
            final FunctionSymbol lhsFunctionSymbol = trans.getLhsFunctionSymbol();
            final boolean isConst = lhsFunctionSymbol.getArity() == 0;
            final Pair<FunctionSymbol, List<Integer>> lhs = new Pair<FunctionSymbol, List<Integer>>(trans.getLhsFunctionSymbol(),
                            trans.getLhsStateParameters());
            Set<Integer> knownStates;
            if (isConst) {
                knownStates = constTransitionsAsMap.get(lhs);
            } else {
                knownStates = transitionsAsMap.get(lhs);
            }

            if (knownStates == null) {
                knownStates = new LinkedHashSet<Integer>();
            }
            for (final Integer state : epsTransClosStates) {
                final Transition<FunctionSymbol, Integer> newTrans = Transition.create(trans.getLhsFunctionSymbol(), trans.getLhsStateParameters(), state);

                transitionsForNewTA.add(newTrans);
                oldPowStates.add(this.sTPS.getPowState(state));
                knownStates.add(state);
                if (isConst) {
                    constTransitionsAsMap.put(lhs, knownStates);
                } else {
                    posArEpsClosedTransitions.add(newTrans);
                }

                transitionsAsMap.put(lhs, knownStates);

            }
        }

        /*
         * compute new quasi-det transitions for old pow states
         */
        for (final Map.Entry<Pair<FunctionSymbol, List<Integer>>, Set<Integer>> entry : transitionsAsMap.entrySet()) {
            final Set<Integer> detPowState = new LinkedHashSet<Integer>();
            for (final Integer state : entry.getValue()) {
                detPowState.addAll(this.sTPS.getPowState(state));
            }

            /*
             * We have to consider all det states as a new pow state (although they may already be known)
             * because we made A quasi-compatible before, i.e. we deleted for example a transition
             * f_0({1,2}, {1,2}) -> {1,2} although transitions like f_0(1,1) -> 1 and f_0(2,2) -> 2
             * exist yet
             */
            this.updateSTPS(detPowState);
            newPowStates.add(detPowState);


            final Pair<FunctionSymbol, List<Integer>> lhs = entry.getKey();
            final Transition<FunctionSymbol, Integer> detTrans = Transition.create(lhs.getKey(), lhs.getValue(), this.sTPS.getState(detPowState));
            transitionsForNewTA.add(detTrans);
            detTransitionsForNewTA.add(detTrans);
        }


        /*
         * compute new quasi-det transitions for new pow states
         */
        while (!newPowStates.isEmpty()) {
            oldPowStates.addAll(newPowStates);
            final Set<Set<Integer>> newlyAddedPowStates = new LinkedHashSet<Set<Integer>>();
            for (final FunctionSymbol f : this.signatureOfTA) {
                if (f.getArity() != 0) {
                    LinkedHashSet<Transition<FunctionSymbol, Set<Integer>>> powerSetTrans = TRSBoundsTA.getSubsumeTransitions(f, newPowStates,
                        posArEpsClosedTransitions, this.sTPS);

                    while (!powerSetTrans.isEmpty()) {
                        final Set<Transition<FunctionSymbol, Integer>> transitionsToConsider = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
                        for (final Transition<FunctionSymbol, Set<Integer>> powTrans : powerSetTrans) {

                            if (this.updateSTPS(powTrans.getRhsState())) {
                                newlyAddedPowStates.add(powTrans.getRhsState());
                            }

                            final Transition<FunctionSymbol, Integer> newTrans = TRSBoundsTA.powTransToTrans(powTrans, this.sTPS);
                            transitionsToConsider.add(newTrans);

                            transitionsForNewTA.add(newTrans);



                            detTransitionsForNewTA.add(newTrans);
                            newTransitions.add(newTrans);

                        }

                        powerSetTrans = TRSBoundsTA.getSubsumeTransitions(f, newPowStates, transitionsToConsider, this.sTPS);
                    }
                }
            }
            newPowStates = newlyAddedPowStates;
        }

        final Set<Set<Integer>> allPowStates = new LinkedHashSet<Set<Integer>>();
        allPowStates.addAll(oldPowStates);
        allPowStates.addAll(newPowStates);
        final LinkedHashSet<Set<Integer>> powFinalStates = TRSBoundsTA.createPowerSetFStates(A.getFinalStates(), allPowStates);
        final Set<Integer> newFinalStates = new LinkedHashSet<Integer>();
        for (final Set<Integer> powFState : powFinalStates) {
            newFinalStates.add(this.sTPS.getState(powFState));
        }
        final Set<Transition<FunctionSymbol, Integer>> transForRC = this.computeTransForRC(transitionsForNewTA, newTransitions);
        transitionsForNewTA.addAll(transForRC);
        newTransitions.addAll(transForRC);
        final TRSBoundsTA.QuasiDeterministicTA newA =
            TRSBoundsTA.QuasiDeterministicTA.create(newFinalStates, transitionsForNewTA, newEpsTransitions, detTransitionsForNewTA, detEpsTransitions);

        return newA;
    }

    private boolean updateSTPS(final Set<Integer> powState) {
        final Integer intState = this.sTPS.getState(powState);
        if (intState == null) {
            this.sTPS.set(this.nextNewState, powState);
            this.nextNewState++;
            return true;
        }
        return false;
    }

    /*
     * Adds to transitionsForNewTA the Transitions to be created to make the new TA raise consistent.
     */
    private Set<Transition<FunctionSymbol, Integer>> computeTransForRC(final Set<Transition<FunctionSymbol, Integer>> transitionsForNewTA,
                    final Set<Transition<FunctionSymbol, Integer>> newTransitions) {
        final Set<Transition<FunctionSymbol, Integer>> transForRC = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();

        for (final Transition<FunctionSymbol, Integer> newTrans : newTransitions) {
            final FunctionSymbol newTransF = newTrans.getLhsFunctionSymbol();
            for (final Transition<FunctionSymbol, Integer> actTrans : transitionsForNewTA) {
                final FunctionSymbol actTransF = actTrans.getLhsFunctionSymbol();
                if (this.enrichment.base(newTransF).equals(this.enrichment.base(actTransF))) {
                    final List<Integer> newTransSP = newTrans.getLhsStateParameters();
                    final List<Integer> actTransSP = actTrans.getLhsStateParameters();
                    if (newTransSP.equals(actTransSP)) {
                        final int heightOfNewTrans = this.enrichment.height(newTransF);
                        final int heightOfActTrans = this.enrichment.height(actTransF);
                        if (heightOfNewTrans > heightOfActTrans) {
                            transForRC.add(Transition.<FunctionSymbol, Integer> create(newTransF, newTransSP, actTrans.getRhsState()));
                        } else if (heightOfActTrans > heightOfNewTrans) {
                            transForRC.add(Transition.<FunctionSymbol, Integer> create(actTransF, actTransSP, newTrans.getRhsState()));

                        }
                    }
                }
            }
        }
        return transForRC;

    }

    /*
     * Builds up romR by using signatureOfTA and the original TRS R
     * Calls actually createER(...) to update romR.
     */
    private void updateRomRAndBound(final Abortion aborter) throws AbortionException {

        for (final FunctionSymbol f : this.signatureOfTA) {
            final int height = this.enrichment.height(f);
            if (height > this.boundedBy) {
                this.boundedBy = height;
            }
        }

        this.romR = this.enrichment.getTRS();
    }

    /*
     * Returns a maximal Set S of terms builded over signature such that for every s element S:
     * base(s) = t and height(f_s) >= height (f_t) for every function symbol f_s = s(pi), f_t = t(pi)
     * where pi is a position.
     */
    private Set<TRSTerm> buildTermsBTOE(final TRSTerm t, final Set<FunctionSymbol> signature) {
        final Set<TRSTerm> termsBTOET = new LinkedHashSet<TRSTerm>();
        if (t.isVariable()) {
            termsBTOET.add(t);
            return termsBTOET;
        } else {
            final TRSFunctionApplication fA = (TRSFunctionApplication) t;
            final Set<ArrayList<TRSTerm>> possibleArgs = new LinkedHashSet<ArrayList<TRSTerm>>();
            possibleArgs.add(new ArrayList<TRSTerm>());
            for (final TRSTerm arg : fA.getArguments()) {
                final Set<TRSTerm> possibleArg = this.buildTermsBTOE(arg, signature);
                final Set<ArrayList<TRSTerm>> oldPossibleArgs = new LinkedHashSet<ArrayList<TRSTerm>>(possibleArgs);
                possibleArgs.clear();
                for (final ArrayList<TRSTerm> args : oldPossibleArgs) {
                    for (final TRSTerm newArg : possibleArg) {
                        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args);
                        newArgs.add(newArg);
                        possibleArgs.add(newArgs);
                    }

                }
            }

            final FunctionSymbol root = fA.getRootSymbol();
            for (final FunctionSymbol newRoot : signature) {
                if (this.enrichment.base(root).equals(this.enrichment.base(newRoot))) {
                    if (this.enrichment.height(root) <= this.enrichment.height(newRoot)) {
                        for (final ArrayList<TRSTerm> args : possibleArgs) {
                            termsBTOET.add(TRSTerm.createFunctionApplication(newRoot, ImmutableCreator.create(args)));
                        }
                    }
                }
            }
        }

        return termsBTOET;
    }

    /*
     * Returns a tree automaton which has at least all transitions of A. Also updates romR  by using all function symbols for which there is a transition in the tree automaton
     * as the signature of left hand sides of roof(R) (resp. match(R)).
     */
    private TreeAutomaton<FunctionSymbol, Integer> resolveConflictsAndExtendSignatureOfTA(final TreeAutomaton<FunctionSymbol, Integer> A,
                    final Collection<Conflict> conflicts, final Abortion aborter) throws AbortionException {
        if (this.wTBTA == WhenToBuildTAStrategy.BUILD_TA_AFTER_RESOLVING_ALL_CONFLICTS) {
            final Set<Transition<FunctionSymbol, Integer>> resolvingTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
            Map<Integer, Set<Integer>> epsTransitions = new LinkedHashMap<Integer, Set<Integer>>();
            for (final Conflict c : conflicts) {
                aborter.checkAbortion();
                final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResConflict =
                    this.resolveConflict(A, c, this.cRS, aborter);

                resolvingTransitions.addAll(transToResConflict.x);
                epsTransitions = TreeAutomatonHelper.<Integer> unionEpsTransitions(epsTransitions, transToResConflict.y);
                final TRSTerm t = c.getTerm();
                for (final FunctionSymbol f : t.getFunctionSymbols()) {

                    this.signatureOfTA.add(f);

                }
            }

            final Set<Transition<FunctionSymbol, Integer>> oldTransitions = A.getTransitions();
            final Set<Transition<FunctionSymbol, Integer>> transForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>(oldTransitions);
            transForNewTA.addAll(resolvingTransitions);
            final Set<Integer> finalStatesForNewTA = new LinkedHashSet<Integer>(A.getFinalStates());
            final Map<Integer, Set<Integer>> epsTransForNewTA = TreeAutomatonHelper.unionEpsTransitions(A.getEpsTransitions(), epsTransitions);
            final TreeAutomaton<FunctionSymbol, Integer> newA = TreeAutomaton.<FunctionSymbol, Integer> create(finalStatesForNewTA, transForNewTA,
                epsTransForNewTA);
            if (this.runtimeComplexity) {
                this.enrichment.SetTAForCurCompConflicts(newA);
            }
            this.enrichment.addToSignature(this.signatureOfTA);
            return newA;
        } else /* wTBTA ==  WhenToBuildTAStrategy.BUILD_TA_AFTER_RESOLVING_ONE_CONFLICT */{
            TreeAutomaton<FunctionSymbol, Integer> newA = A;
            final Set<Transition<FunctionSymbol, Integer>> resolvingTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
            Set<Transition<FunctionSymbol, Integer>> oldTransitions;
            Set<Transition<FunctionSymbol, Integer>> transForNewTA = null;
            Set<Integer> finalStatesForNewTA = null;
            Map<Integer, Set<Integer>> epsTransForNewTA = null;
            Map<Integer, Set<Integer>> epsTransitions = new LinkedHashMap<Integer, Set<Integer>>();

            for (final Conflict c : conflicts) {
                aborter.checkAbortion();
                if (!newA.evaluate(c.getTerm(), c.getStateSubstitution()).contains(c.getTargetState())) {
                    if (Globals.DEBUG_MARCEL) {
                        //Logger.getAnonymousLogger("Conflict To Resolve: " + c);
                    }
                    aborter.checkAbortion();
                    final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResConflict = this.resolveConflict(newA, c, this.cRS,
                        aborter);
                    aborter.checkAbortion();
                    resolvingTransitions.addAll(transToResConflict.x);
                    epsTransitions = TreeAutomatonHelper.<Integer> unionEpsTransitions(epsTransitions, transToResConflict.y);
                    final TRSTerm t = c.getTerm();
                    for (final FunctionSymbol f : t.getFunctionSymbols()) {
                        this.signatureOfTA.add(f);

                    }

                    oldTransitions = newA.getTransitions();
                    transForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>(oldTransitions);
                    transForNewTA.addAll(resolvingTransitions);
                    finalStatesForNewTA = new LinkedHashSet<Integer>(A.getFinalStates());
                    epsTransForNewTA = TreeAutomatonHelper.unionEpsTransitions(A.getEpsTransitions(), epsTransitions);
                    newA = TreeAutomaton.<FunctionSymbol, Integer> create(finalStatesForNewTA, transForNewTA, epsTransForNewTA);
                    if (Globals.DEBUG_MARCEL) {
                        //Logger.getAnonymousLogger("newA: " + newA);
                    }
                }
            }

            if (this.runtimeComplexity) {
                this.enrichment.SetTAForCurCompConflicts(newA);
            }
            this.enrichment.addToSignature(this.signatureOfTA);
            return newA;
        }
    }


    private TreeAutomaton<FunctionSymbol, Integer> resolveQCompConflictsAndExtendSignatureOfRomR(final TRSBoundsTA.QuasiDeterministicTA qDetA,
                    final Set<Conflict> conflicts, final Abortion aborter) throws AbortionException {
        if (this.wTBTA == WhenToBuildTAStrategy.BUILD_TA_AFTER_RESOLVING_ALL_CONFLICTS) {
            final TreeAutomaton<FunctionSymbol, Integer> A = qDetA.getTA();

            final Set<Transition<FunctionSymbol, Integer>> resolvingTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
            Map<Integer, Set<Integer>> epsTransitions = new LinkedHashMap<Integer, Set<Integer>>();
            for (final Conflict c : conflicts) {
                final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResConflict =
                    this.resolveConflict(A, c, this.cRS, aborter);

                resolvingTransitions.addAll(transToResConflict.x);
                epsTransitions = TreeAutomatonHelper.<Integer> unionEpsTransitions(epsTransitions, transToResConflict.y);
                final TRSTerm t = c.getTerm();
                for (final FunctionSymbol f : t.getFunctionSymbols()) {

                    this.signatureOfTA.add(f);

                }
            }

            final Set<Transition<FunctionSymbol, Integer>> oldTransitions = A.getTransitions();
            final Set<Transition<FunctionSymbol, Integer>> transForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>(oldTransitions);
            transForNewTA.addAll(resolvingTransitions);
            final Set<Integer> finalStatesForNewTA = new LinkedHashSet<Integer>(A.getFinalStates());
            final Set<Transition<FunctionSymbol, Integer>> transForRC = this.computeTransForRC(transForNewTA, resolvingTransitions);
            transForNewTA.addAll(transForRC);
            this.deleteUnnecessaryTransBecauseOfQC(transForNewTA, resolvingTransitions);
            final Map<Integer, Set<Integer>> epsTransForNewTA = TreeAutomatonHelper.unionEpsTransitions(A.getEpsTransitions(), epsTransitions);
            final TreeAutomaton<FunctionSymbol, Integer> newA = TreeAutomaton.<FunctionSymbol, Integer> create(finalStatesForNewTA, transForNewTA,
                epsTransForNewTA);

            this.enrichment.addToSignature(this.signatureOfTA);
            return newA;
        } else /* wTBTA ==  WhenToBuildTAStrategy.BUILD_TA_AFTER_RESOLVING_ONE_CONFLICT */{
            TreeAutomaton<FunctionSymbol, Integer> newA = qDetA.getTA();

            for (final Conflict c : conflicts) {
                if (this.isQCompConflict(newA, c)) {
                    if (Globals.DEBUG_MARCEL) {
                        //Logger.getAnonymousLogger("Conflict To Resolve: " + c);
                    }

                    final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResConflict =
                        this.resolveConflict(newA, c, this.cRS, aborter);

                    final Set<Transition<FunctionSymbol, Integer>> resolvingTransitions = transToResConflict.x;
                    final Map<Integer, Set<Integer>> epsTransitions = transToResConflict.y;
                    final TRSTerm t = c.getTerm();
                    for (final FunctionSymbol f : t.getFunctionSymbols()) {
                        this.signatureOfTA.add(f);
                    }

                    final Set<Transition<FunctionSymbol, Integer>> oldTransitions = newA.getTransitions();
                    final Set<Transition<FunctionSymbol, Integer>> transForNewTA = new LinkedHashSet<Transition<FunctionSymbol, Integer>>(oldTransitions);
                    final Set<Integer> finalStatesForNewTA = new LinkedHashSet<Integer>(newA.getFinalStates());
                    final Map<Integer, Set<Integer>> epsTransForNewTA = TreeAutomatonHelper.unionEpsTransitions(newA.getEpsTransitions(), epsTransitions);
                    transForNewTA.addAll(resolvingTransitions);
                    final Set<Transition<FunctionSymbol, Integer>> transForRC = this.computeTransForRC(transForNewTA, resolvingTransitions);
                    transForNewTA.addAll(transForRC);

                    this.deleteUnnecessaryTransBecauseOfQC(transForNewTA, resolvingTransitions);
                    this.deleteUnnecessaryTransBecauseOfQC(transForNewTA, transForRC);

                    newA = TreeAutomaton.<FunctionSymbol, Integer> create(finalStatesForNewTA, transForNewTA, epsTransForNewTA);
                    if (Globals.DEBUG_MARCEL) {
                        //Logger.getAnonymousLogger("newA: " + newA);
                    }
                }
            }
            this.enrichment.addToSignature(this.signatureOfTA);
            return newA;
        }
    }

    private boolean isQCompConflict(final TreeAutomaton<FunctionSymbol, Integer> A, final Conflict c) {
        final TRSTerm t = c.getTerm();
        final StateSubstitution<Integer> sigma = c.getStateSubstitution();
        final int targetState = c.getTargetState();
        final Set<TRSTerm> termsBTOET = this.buildTermsBTOE(t, this.signatureOfTA);
        final Set<Integer> statesAfterEvalTermBTOERhs = new LinkedHashSet<Integer>();

        for (final TRSTerm s : termsBTOET) {
            statesAfterEvalTermBTOERhs.addAll(A.evaluate(s, sigma));
        }

        if (statesAfterEvalTermBTOERhs.contains(targetState)) {
            return false;
        }

        return true;
    }

    private void deleteUnnecessaryTransBecauseOfQC(final Set<Transition<FunctionSymbol, Integer>> transForNewTA,
                    final Set<Transition<FunctionSymbol, Integer>> resolvingTransitions) {
        // Delete Transitions trans1: lhs --> rhs, where there is already a transitions trans2: lhs' --> rhs and
        // and base(trans1.getLhsFunctionSymbol()) < base(trans2.getLhsFunctionSymbol())
        // and trans1.getLhsStateParameters() equals trans2.getStateParameters()
        final Set<Transition<FunctionSymbol, Integer>> copy = new LinkedHashSet<Transition<FunctionSymbol, Integer>>(transForNewTA);
        for (final Transition<FunctionSymbol, Integer> trans1 : resolvingTransitions) {
            for (final Transition<FunctionSymbol, Integer> trans2 : copy) {
                final FunctionSymbol t1F = trans1.getLhsFunctionSymbol();
                final FunctionSymbol t2F = trans2.getLhsFunctionSymbol();
                if (this.enrichment.base(t1F).equals(this.enrichment.base(t2F))) {
                    if (trans1.getLhsStateParameters().equals(trans2.getLhsStateParameters())) {
                        if (trans1.getRhsState().equals(trans2.getRhsState())) {

                            if (this.enrichment.height(t1F) < this.enrichment.height(t2F)) {

                                transForNewTA.remove(trans1);
                            }

                            else if (this.enrichment.height(t1F) > this.enrichment.height(t2F)) {

                                transForNewTA.remove(trans2);
                            }
                        }
                    }
                }
            }
        }

    }

    /*
     * returns a set of transitions and a set of epsilon transitions to resolve the conflict c for the tree automaton A by the strategy cRS.
     */
    private Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> resolveConflict(final TreeAutomaton<FunctionSymbol, Integer> A,
                    final Conflict c, final ConflictResolvingStrategy cRS, final Abortion aborter) throws AbortionException {
        aborter.checkAbortion();
        final TRSTerm t = c.getTerm();
        final StateSubstitution<Integer> sigma = c.getStateSubstitution();
        final Rule evokingRule = c.getEvokingRule();
        final int targetState = c.getTargetState();
        final Set<Transition<FunctionSymbol, Integer>> resolvingTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
        Map<Integer, Set<Integer>> epsTransitions = new LinkedHashMap<Integer, Set<Integer>>();
        if (t.isVariable()) {
            // if t is a variable, we resolve this conflict by adding a epsilon transition from the state given by sigma to the targetState
            final LinkedHashSet<Integer> newEpsTransRhs = new LinkedHashSet<Integer>();
            newEpsTransRhs.add(targetState);
            epsTransitions.put(sigma.getMap().get(t), newEpsTransRhs);
            return new Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>>(resolvingTransitions, epsTransitions);
        }
        if (cRS == ConflictResolvingStrategy.NSFEPS) {

            final TRSFunctionApplication fA = (TRSFunctionApplication) t;
            final FunctionSymbol rootSymbol = fA.getRootSymbol();
            final List<Integer> stateArgsForRoot = new ArrayList<Integer>();
            for (final TRSTerm arg : fA.getArguments()) {
                if (arg.isVariable()) {
                    final TRSVariable x = (TRSVariable) arg;
                    stateArgsForRoot.add(sigma.getMap().get(x));
                } else if (arg instanceof TRSFunctionApplication) {
                    stateArgsForRoot.add(this.nextNewState);
                    final Conflict newConflict = new Conflict(arg, sigma, this.nextNewState, evokingRule);

                    if (this.isRaiseBound(this.bound)) {
                        final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                        initSTPS.add(this.nextNewState);
                        this.sTPS.set(this.nextNewState, initSTPS);
                    }

                    this.nextNewState++;
                    final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResNewConflict =
                        this.resolveConflict(A, newConflict, ConflictResolvingStrategy.NSFEPS, aborter);
                    resolvingTransitions.addAll(transToResNewConflict.x);
                    epsTransitions = TreeAutomatonHelper.<Integer> unionEpsTransitions(epsTransitions, transToResNewConflict.y);
                }
            }
            final Transition<FunctionSymbol, Integer> newTrans = Transition.<FunctionSymbol, Integer> create(rootSymbol, stateArgsForRoot, targetState);
            resolvingTransitions.add(newTrans);

        } else if (cRS == ConflictResolvingStrategy.KMS) {

            final Set<Pair<List<StateSubstTerm>, List<Integer>>> computedContexts = TRSBoundsCRHelper.computeKMSContexts(A, c);


            int min = -1;
            Pair<List<StateSubstTerm>, List<Integer>> minCompCon = null;

            for (final Pair<List<StateSubstTerm>, List<Integer>> compCon : computedContexts) {
                int actSize = 0;
                for (final StateSubstTerm innCon : compCon.getKey()) {
                    actSize += innCon.size();

                }
                if (min < 0) {
                    min = actSize;
                    minCompCon = compCon;
                } else if (actSize < min) {
                    min = actSize;
                    minCompCon = compCon;
                }
            }

            final List<StateSubstTerm> kmsCon = minCompCon.getKey();
            final List<Integer> targetStates = minCompCon.getValue();

            if (Globals.useAssertions) {
                assert (!kmsCon.isEmpty());
            }

            for (int i = 0; i < kmsCon.size(); i++) {
                final TRSTerm newT = kmsCon.get(i).getT();
                final StateSubstitution<Integer> newSigma = kmsCon.get(i).getSigma();
                final int newTargetState = targetStates.get(i);
                final Conflict newConflict = new Conflict(newT, newSigma, newTargetState, evokingRule);
                final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResNewConflict = this.resolveConflict(A, newConflict,
                    ConflictResolvingStrategy.MYCRS2, aborter);
                resolvingTransitions.addAll(transToResNewConflict.getKey());
                epsTransitions = TreeAutomatonHelper.<Integer> unionEpsTransitions(epsTransitions, transToResNewConflict.getValue());
            }

        } else if (cRS == ConflictResolvingStrategy.MYCRS) {
            final TRSFunctionApplication fA = (TRSFunctionApplication) t;
            final FunctionSymbol rootSymbol = fA.getRootSymbol();
            final List<Integer> stateArgsForRoot = new ArrayList<Integer>();
            final List<TRSTerm> rootArguments = fA.getArguments();

            final Set<List<Integer>> reusableStateParamsForRoot = A.getAllStateParamsWith(rootSymbol, targetState);
            boolean fAHasOnlyVarArgs = true;
            for (final TRSTerm arg : rootArguments) {
                if (!arg.isVariable()) {
                    fAHasOnlyVarArgs = false;
                }
            }
            if (reusableStateParamsForRoot.isEmpty() || fAHasOnlyVarArgs) {
                for (final TRSTerm arg : fA.getArguments()) {
                    final Set<Integer> argStates = A.evaluate(arg, sigma);
                    if (argStates.isEmpty()) {
                        //If the argument cannot currently be evaluated to any state, we use one new state here
                        final Conflict newConflict = new Conflict(arg, sigma, this.nextNewState, evokingRule);
                        stateArgsForRoot.add(this.nextNewState);

                        if (this.isRaiseBound(this.bound)) {
                            final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                            initSTPS.add(this.nextNewState);
                            this.sTPS.set(this.nextNewState, initSTPS);
                        }

                        this.nextNewState++;

                        final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResNewConflict =
                            this.resolveConflict(A, newConflict, ConflictResolvingStrategy.MYCRS, aborter);
                        resolvingTransitions.addAll(transToResNewConflict.x);
                        epsTransitions = TreeAutomatonHelper.<Integer> unionEpsTransitions(epsTransitions, transToResNewConflict.y);
                    } else {
                        // Reuse one of the states, to which the argument can be evaluated
                        stateArgsForRoot.add(argStates.iterator().next());
                    }
                }
                final Transition<FunctionSymbol, Integer> newTrans = Transition.<FunctionSymbol, Integer> create(rootSymbol, stateArgsForRoot, targetState);
                resolvingTransitions.add(newTrans);
            } else {
                final Map<List<Integer>, Integer> countMap = new LinkedHashMap<List<Integer>, Integer>(); //counts how many states can be reused

                for (final List<Integer> l : reusableStateParamsForRoot) {
                    countMap.put(l, this.computeCount(l, rootArguments, sigma, A));
                }

                List<Integer> stateParamsToBeReused = null;
                //Reuse transition with smallest count
                final int curLowestValue = Integer.MAX_VALUE;
                for (final Map.Entry<List<Integer>, Integer> entry : countMap.entrySet()) {
                    if (entry.getValue() < curLowestValue) {
                        stateParamsToBeReused = entry.getKey();
                    }

                }

                //Here we copy stateParamsToBereused to a new array list to make it mutable
                stateParamsToBeReused = new ArrayList<Integer>(stateParamsToBeReused);
                int index = 0;
                for (final TRSTerm arg : rootArguments) {
                    if (arg.isVariable()) {
                        final TRSVariable x = (TRSVariable) arg;
                        if (sigma.getMap().get(x) != stateParamsToBeReused.get(index)) {
                            stateParamsToBeReused.set(index, sigma.getMap().get(x));
                            final Map<TRSVariable, Integer> newSigmaMap = new LinkedHashMap<TRSVariable, Integer>(sigma.getMap());
                            newSigmaMap.put(x, stateParamsToBeReused.get(index));

                        }

                    }
                    index++;
                }

                final Transition<FunctionSymbol, Integer> newTrans =
                    Transition.<FunctionSymbol, Integer> create(rootSymbol, stateParamsToBeReused, targetState);
                resolvingTransitions.add(newTrans);

                if (Globals.useAssertions) {
                    assert (stateParamsToBeReused != null);
                }
                index = 0;
                for (final TRSTerm arg : rootArguments) {

                    final Set<Integer> argStates = A.evaluate(arg, sigma);

                    if (!(argStates.contains(stateParamsToBeReused.get(index)))) {
                        final Conflict newConflict = new Conflict(arg, sigma, stateParamsToBeReused.get(index), evokingRule);
                        final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResNewConflict =
                            this.resolveConflict(A, newConflict, ConflictResolvingStrategy.MYCRS, aborter);
                        resolvingTransitions.addAll(transToResNewConflict.x);
                        epsTransitions = TreeAutomatonHelper.<Integer> unionEpsTransitions(epsTransitions, transToResNewConflict.y);
                    }

                    index++;
                }

            }

        } else if (cRS == ConflictResolvingStrategy.MYCRS2) {

            final Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> resolvingTranss = this.confResolver.resolveConflict(A, c,
                aborter);
            this.nextNewState = this.confResolver.getNextNewState();
            return resolvingTranss;
        }

        return new Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>>(resolvingTransitions, epsTransitions);
    }

    /*
     * Computes how many new transitions would be needed, if we want to reuse a transition with state parameters l
     */
    private int computeCount(final List<Integer> l, final List<TRSTerm> arguments, final StateSubstitution<Integer> sigma, final TreeAutomaton<FunctionSymbol, Integer> A) {
        int count = 0;
        for (int i = 0; i < l.size(); i++) {
            final int state = l.get(i);
            final TRSTerm arg = arguments.get(i);
            if (arg.isVariable()) {
                final TRSVariable x = (TRSVariable) arg;
                if (sigma.getMap().get(x) != state) {
                    if (count == 0) {
                        count = 1;
                    }
                }
            } else {
                final TRSFunctionApplication fA = (TRSFunctionApplication) arg;
                final FunctionSymbol rootSymbol = fA.getRootSymbol();
                final Set<Integer> statesForArg = A.evaluate(arg, sigma);
                if (!statesForArg.contains(state)) {
                    count++;
                    for (final List<Integer> l2 : A.getAllStateParamsWith(rootSymbol, this.nextNewState)) {
                        count += this.computeCount(l2, fA.getArguments(), sigma, A);
                    }
                }
            }
        }

        return count;
    }

    /*
     * Collects all compatibility conflict with the tree automaton A
     */
    private Set<Conflict> collectAllCompatibleConflicts(final TreeAutomaton<FunctionSymbol, Integer> A, final Set<Rule> trs, final Abortion aborter)
                    throws AbortionException {
        final Set<Conflict> conflicts = new LinkedHashSet<Conflict>();
        final Set<Integer> allStates = A.getAllStates();

        for (final Rule r : trs) {
            final TRSFunctionApplication lhs = r.getLeft();
            final TRSTerm rhs = r.getRight();

            for (final Integer targetState : allStates) {
                aborter.checkAbortion();
                final Set<StateSubstitution<Integer>> stateSubstitutions = TRSBoundsTA.createStateSubstitutions(A, lhs, targetState, allStates);
                for (final StateSubstitution<Integer> sigma : stateSubstitutions) {
                    // Delete var substitution which don't exist on Rhss
                    final Map<TRSVariable, Integer> newStateSubs = new LinkedHashMap<TRSVariable, Integer>();
                    final Set<TRSVariable> varsOfRhs = rhs.getVariables();
                    for (final Map.Entry<TRSVariable, Integer> entry : sigma.getMap().entrySet()) {
                        final TRSVariable x = entry.getKey();
                        if (varsOfRhs.contains(x)) {
                            newStateSubs.put(x, entry.getValue());
                        }
                    }

                    final StateSubstitution<Integer> newSigma = StateSubstitution.create(newStateSubs);

                    final Pair<TRSTerm, StateSubstitution<Integer>> pair = new Pair<TRSTerm, StateSubstitution<Integer>>(rhs, newSigma);
                    Set<Integer> alreadyKnownPath = this.alreadyFoundConflicts.get(pair);
                    if (alreadyKnownPath == null) {
                        alreadyKnownPath = new LinkedHashSet<Integer>();
                    }
                    if (!alreadyKnownPath.contains(targetState)) {
                        final Set<Integer> statesAfterEvaluatingRhs = A.evaluate(rhs, newSigma);
                        alreadyKnownPath.addAll(statesAfterEvaluatingRhs);
                        this.alreadyFoundConflicts.put(pair, alreadyKnownPath);
                        if (!statesAfterEvaluatingRhs.contains(targetState)) {
                            conflicts.add(new Conflict(rhs, newSigma, targetState, r));

                        }
                    }

                }
            }

        }
        return conflicts;
    }

    private Set<Conflict> collectAllQCompatibleConflicts(final TRSBoundsTA.QuasiDeterministicTA qDetA, final Abortion aborter) throws AbortionException {

        final TreeAutomaton<FunctionSymbol, Integer> detA =
            new TreeAutomaton<FunctionSymbol, Integer>(qDetA.getDetFinalStates(), qDetA.getDetTransitions(), qDetA.getDetEpsTransitions());

        final Set<Conflict> conflicts = new LinkedHashSet<Conflict>();
        final Set<Integer> allStates = detA.getAllRhsStates();

        final Set<FunctionSymbol> signatureOfRomR = detA.getAllFunctionSymbols();

        for (final Rule r : this.romR) {
            final TRSFunctionApplication lhs = r.getLeft();
            final TRSTerm rhs = r.getRight();
            final Set<TRSTerm> termsBTOERhs = this.buildTermsBTOE(rhs, signatureOfRomR);

            for (final Integer targetState : allStates) {
                aborter.checkAbortion();

                final Set<StateSubstitution<Integer>> stateSubstitutions = TRSBoundsTA.createStateSubstitutions(detA, lhs, targetState, allStates);

                for (final StateSubstitution<Integer> sigma : stateSubstitutions) {

                    // Delete var substitution which don't exist on Rhss
                    final Map<TRSVariable, Integer> newStateSubs = new LinkedHashMap<TRSVariable, Integer>();
                    final Set<TRSVariable> varsOfRhs = rhs.getVariables();
                    for (final Map.Entry<TRSVariable, Integer> entry : sigma.getMap().entrySet()) {
                        final TRSVariable x = entry.getKey();
                        if (varsOfRhs.contains(x)) {
                            newStateSubs.put(x, entry.getValue());
                        }
                    }

                    final StateSubstitution<Integer> newSigma = StateSubstitution.create(newStateSubs);


                    final Set<Integer> statesAfterEvalTermBTOERhs = new LinkedHashSet<Integer>();

                    boolean pathToTargetAlreadyKnown = false;

                    for (final TRSTerm t : termsBTOERhs) {
                        final Pair<TRSTerm, StateSubstitution<Integer>> pair = new Pair<TRSTerm, StateSubstitution<Integer>>(t, newSigma);
                        Set<Integer> alreadyKnownPath = this.alreadyFoundConflicts.get(pair);
                        if (alreadyKnownPath == null) {
                            alreadyKnownPath = new LinkedHashSet<Integer>();
                        }
                        if (alreadyKnownPath.contains(targetState)) {
                            pathToTargetAlreadyKnown = true;
                            break;
                        }

                        statesAfterEvalTermBTOERhs.addAll(alreadyKnownPath);
                    }

                    if (!pathToTargetAlreadyKnown) {
                        for (final TRSTerm t : termsBTOERhs) {
                            aborter.checkAbortion();
                            final Pair<TRSTerm, StateSubstitution<Integer>> pair = new Pair<TRSTerm, StateSubstitution<Integer>>(t, newSigma);
                            Set<Integer> alreadyKnownPath = this.alreadyFoundConflicts.get(pair);
                            if (alreadyKnownPath == null) {
                                alreadyKnownPath = new LinkedHashSet<Integer>();
                            }
                            if (!alreadyKnownPath.contains(targetState)) {
                                final Set<Integer> evaluatedToStates = qDetA.evaluate(t, newSigma);
                                alreadyKnownPath.addAll(evaluatedToStates);
                                this.alreadyFoundConflicts.put(pair, alreadyKnownPath);
                                statesAfterEvalTermBTOERhs.addAll(evaluatedToStates);
                            }

                            statesAfterEvalTermBTOERhs.addAll(alreadyKnownPath);
                        }

                        if (!statesAfterEvalTermBTOERhs.contains(targetState)) {
                            conflicts.add(new Conflict(rhs, newSigma, targetState, r));
                        }
                    }
                }
            }
        }

        return conflicts;
    }

    /*
     * Returns Tree Automaton A to start the contruction with
     */
    private Pair<TreeAutomaton<FunctionSymbol, Integer>, Set<Integer>> getStartAutomaton() {
        TreeAutomaton<FunctionSymbol, Integer> A = null;
        final Set<Transition<FunctionSymbol, Integer>> transitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
        final Set<Integer> finalStates = new LinkedHashSet<Integer>();
        final Map<Integer, Set<Integer>> epsTransitions = new LinkedHashMap<Integer, Set<Integer>>();
        List<Integer> stateArgs = new ArrayList<Integer>();
        final Set<Integer> iteratedStates = new LinkedHashSet<Integer>(); // the set of special final states for CPF output

        if (this.sTAS == STAStrategy.OOS) {
            // create final States
            finalStates.add(this.nextNewState);
            iteratedStates.add(this.nextNewState);
            // create Transitions
            for (final FunctionSymbol f : this.signatureOfTA) {
                for (int i = 0; i < f.getArity(); i++) {
                    stateArgs.add(this.nextNewState);
                }
                final Transition<FunctionSymbol, Integer> trans = Transition.<FunctionSymbol, Integer> create(f, stateArgs, this.nextNewState);
                transitions.add(trans);
                stateArgs = new ArrayList<Integer>();
            }
            if (this.isRaiseBound(this.bound)) {
                final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                initSTPS.add(this.nextNewState);
                this.sTPS.set(this.nextNewState, initSTPS);
            }
            this.nextNewState++;
            //No eps transitions are constructed
        } else if (this.sTAS == STAStrategy.OSFEFS) {
            int fState = this.nextNewState;
            final int newState = this.nextNewState;
            final int numberOfNewStates = this.signatureOfTA.size();

            for (final FunctionSymbol f : this.signatureOfTA) {
                // create f(q_1,...,q_n) -> q_f for every state q_1,...,q_n used in the start automaton
                for (int i = 0; i < Math.pow(numberOfNewStates, f.getArity()); i++) {
                    int next = i;
                    for (int j = 0; j < f.getArity(); j++) {
                        final int state = newState + (next % numberOfNewStates);
                        stateArgs.add(state);
                        iteratedStates.add(state);
                        next /= numberOfNewStates;
                    }
                    final Transition<FunctionSymbol, Integer> trans = Transition.<FunctionSymbol, Integer> create(f, stateArgs, fState);
                    transitions.add(trans);

                    stateArgs = new ArrayList<Integer>();
                }
                // each state in this automaton is a final state, so we simply add here the current fState
                finalStates.add(fState);
                iteratedStates.add(fState);

                if (this.isRaiseBound(this.bound)) {
                    final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                    initSTPS.add(fState);
                    this.sTPS.set(fState, initSTPS);
                }

                fState++;
            }

            this.nextNewState = newState + numberOfNewStates;
            // no epsTransitions are constructed
        } else if (this.sTAS == STAStrategy.RC_SPLIT || this.sTAS == STAStrategy.DP_SPLIT) {

            if (Globals.useAssertions) {
                assert (this.definedSymbols != null);
            }

            final Set<FunctionSymbol> constructorSymbols = new LinkedHashSet<FunctionSymbol>(this.signatureOfTA);
            for (final FunctionSymbol defined : this.definedSymbols) {
                constructorSymbols.remove(this.enrichment.lift(defined, 0));
            }

            int constrState = this.nextNewState;
            int newState = this.nextNewState;
            final int numberOfConstrStates = constructorSymbols.size();

            for (final FunctionSymbol f : constructorSymbols) {
                // create f(q_1,...,q_n) -> q_f for every constr state q_1,...,q_n used in the start automaton
                for (int i = 0; i < Math.pow(numberOfConstrStates, f.getArity()); i++) {
                    int next = i;
                    for (int j = 0; j < f.getArity(); j++) {
                        final int state = newState + (next % numberOfConstrStates);
                        stateArgs.add(state);
                        iteratedStates.add(state);
                        next /= numberOfConstrStates;
                    }
                    final Transition<FunctionSymbol, Integer> trans = Transition.<FunctionSymbol, Integer> create(f, stateArgs, constrState);
                    transitions.add(trans);

                    stateArgs = new ArrayList<Integer>();
                }


                if (this.isRaiseBound(this.bound)) {
                    final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                    initSTPS.add(constrState);
                    this.sTPS.set(constrState, initSTPS);
                }

                constrState++;
            }

            int defState = this.nextNewState + constructorSymbols.size();
            newState = this.nextNewState;

            for (final FunctionSymbol f : this.definedSymbols) {
                // create f(q_1,...,q_n) -> q_f for every constr state q_1,...,q_n used in the start automaton
                for (int i = 0; i < Math.pow(numberOfConstrStates, f.getArity()); i++) {
                    int next = i;
                    for (int j = 0; j < f.getArity(); j++) {
                        stateArgs.add(newState + (next % numberOfConstrStates));
                        next /= numberOfConstrStates;
                    }
                    final Transition<FunctionSymbol, Integer> trans = Transition.<FunctionSymbol, Integer> create(this.enrichment.lift(f, 0), stateArgs,
                        defState);
                    transitions.add(trans);

                    stateArgs = new ArrayList<Integer>();
                }

                finalStates.add(defState);

                if (this.isRaiseBound(this.bound)) {
                    final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                    initSTPS.add(defState);
                    this.sTPS.set(defState, initSTPS);
                }

                defState++;

            }

            this.nextNewState = defState;
        } else if (this.sTAS == STAStrategy.RC_DEFSPLIT || this.sTAS == STAStrategy.DP_DEFSPLIT) {

            if (Globals.useAssertions) {
                assert (this.definedSymbols != null);
            }

            final Set<FunctionSymbol> constructorSymbols = new LinkedHashSet<FunctionSymbol>(this.signatureOfTA);
            for (final FunctionSymbol defined : this.definedSymbols) {
                constructorSymbols.remove(this.enrichment.lift(defined, 0));
            }

            final int constrState = this.nextNewState;
            iteratedStates.add(constrState);

            for (final FunctionSymbol f : constructorSymbols) {
                for (int j = 0; j < f.getArity(); j++) {
                    stateArgs.add(constrState);
                }
                final Transition<FunctionSymbol, Integer> trans = Transition.<FunctionSymbol, Integer> create(f, stateArgs, constrState);
                transitions.add(trans);

                stateArgs = new ArrayList<Integer>();
            }

            if (this.isRaiseBound(this.bound)) {
                final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                initSTPS.add(this.nextNewState);
                this.sTPS.set(this.nextNewState, initSTPS);
            }
            this.nextNewState++;

            int defState = this.nextNewState;

            for (final FunctionSymbol f : this.definedSymbols) {

                for (int j = 0; j < f.getArity(); j++) {
                    stateArgs.add(constrState);

                }
                final Transition<FunctionSymbol, Integer> trans = Transition.<FunctionSymbol, Integer> create(this.enrichment.lift(f, 0), stateArgs,
                    defState);
                transitions.add(trans);

                stateArgs = new ArrayList<Integer>();

                finalStates.add(defState);

                if (this.isRaiseBound(this.bound)) {
                    final Set<Integer> initSTPS = new LinkedHashSet<Integer>();
                    initSTPS.add(defState);
                    this.sTPS.set(defState, initSTPS);
                }

                defState++;

            }

            this.nextNewState = defState;
        }

        A = TreeAutomaton.create(finalStates, transitions, epsTransitions);
        return new Pair<>(A, iteratedStates);
    }

}
