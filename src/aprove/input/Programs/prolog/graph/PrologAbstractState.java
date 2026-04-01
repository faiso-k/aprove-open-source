package aprove.input.Programs.prolog.graph;

import java.util.*;

import org.json.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * Abstract state for symbolic evaluation of Prolog programs.<br><br>
 *
 * Created: Dec 4, 2006<br>
 * Last modified: Aug 18, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologAbstractState implements PrettyStringable, Immutable, JSONExport {

    /**
     * @param instance
     * @param of
     * @param aborter For abortions.
     * @return
     */
    public static PrologSubstitution calculateInstanceMatcher(
        PrologAbstractState instance,
        PrologAbstractState of,
        boolean noGroundLoss,
        Abortion aborter
    ) {
        if (instance.getState().size() != of.getState().size()) {
            return null;
        }
        PrologSubstitution res = new PrologSubstitution();
        Set<PrologNonAbstractVariable> used = new LinkedHashSet<PrologNonAbstractVariable>();
        Set<PrologNonAbstractVariable> in = new LinkedHashSet<PrologNonAbstractVariable>();
        for (int i = 0; i < instance.getState().size(); i++) {
            if (
                !PrologAbstractState.calculateInstanceMatcher(
                    instance.getState().get(i),
                    of.getState().get(i),
                    instance.getKnowledgeBase(),
                    of.getKnowledgeBase(),
                    used,
                    in,
                    res
                )
            ) {
                return null;
            }
        }
        if (PrologAbstractState.checkInstanceMatcher(instance, of, res, used, in, noGroundLoss, aborter)) {
            return res;
        }
        return null;
    }

    public static int calculateMaximalStateLengthForInstance(
        PrologAbstractState instance,
        PrologAbstractState of,
        boolean noGroundLoss,
        Abortion aborter
    ) {
        for (int i = instance.getState().size(); i > 0; i--) {
            List<GoalElement> state = new ArrayList<GoalElement>();
            for (int j = 0; j < i; j++) {
                state.add(instance.getState().get(j));
            }
            if (
                PrologAbstractState.calculateInstanceMatcher(
                    new PrologAbstractState(state, instance.getKnowledgeBase()),
                    of,
                    noGroundLoss,
                    aborter
                ) != null
            ) {
                return i;
            }
        }
        return 0;
    }

    public static boolean checkInstanceMatcher(
        PrologAbstractState instance,
        PrologAbstractState of,
        PrologSubstitution mu,
        boolean noGroundLoss,
        Abortion aborter
    ) {
        Set<PrologNonAbstractVariable> in = new LinkedHashSet<PrologNonAbstractVariable>();
        Set<PrologNonAbstractVariable> used = new LinkedHashSet<PrologNonAbstractVariable>();
        for (PrologVariable v : mu.keySet()) {
            if (v.isNonAbstractVariable()) {
                used.add((PrologNonAbstractVariable) v);
            }
        }
        for (GoalElement e : of.getState()) {
            if (!e.isQuestionMark()) {
                in.addAll(e.getTerm().createSetOfAllNonAbstractVariables());
            }
        }
        return PrologAbstractState.checkInstanceMatcher(instance, of, mu, used, in, noGroundLoss, aborter);
    }

    /**
     *
     */
    public static PrologAbstractState createCleanedState(PrologAbstractState state) {
        return new PrologAbstractState(state.getState(), state.getKnowledgeBase().reduceToState(state.getState()));
    }

    public static PrologAbstractState createEmptyState(SMTSolverFactory factory, SMTLIBLogic logic) {
        return new PrologAbstractState(new ArrayList<GoalElement>(), KnowledgeBase.createEmpty(factory, logic));
    }

    public static PrologAbstractState createErrorState(SMTSolverFactory factory, SMTLIBLogic logic) {
        return new ErrorState(factory, logic);
    }

    public static PrologAbstractState createFromTerm(PrologTerm head, KnowledgeBase kb) {
        List<GoalElement> list = new ArrayList<GoalElement>();
        list.add(new GoalElement(head));
        return new PrologAbstractState(list, kb);
    }

    public static PrologAbstractState createWithEmptyKnowledgeBase(
        PrologTerm term,
        SMTSolverFactory factory,
        SMTLIBLogic logic
    ) {
        return PrologAbstractState.createFromTerm(term, KnowledgeBase.createEmpty(factory, logic));
    }

    /**
     * @param instance
     * @param of
     * @param ofBase
     * @param instanceBase
     * @param used
     * @param in
     * @param res
     * @return
     */
    private static boolean calculateInstanceMatcher(
        GoalElement instance,
        GoalElement of,
        KnowledgeBase instanceBase,
        KnowledgeBase ofBase,
        Set<PrologNonAbstractVariable> used,
        Set<PrologNonAbstractVariable> in,
        PrologSubstitution res
    ) {
        if (instance.isQuestionMark()) {
            if (of.isQuestionMark()) {
                return instance.getScope() == of.getScope();
            } else {
                return false;
            }
        } else if (instance.hasApplicableClause()) {
            if (!of.isQuestionMark() && of.hasApplicableClause()) {
                if (instance.getApplicableClause() == of.getApplicableClause()) {
                    in.addAll(of.getTerm().createSetOfAllNonAbstractVariables());
                    return PrologAbstractState.calculateInstanceMatcher(
                        instance.getTerm(),
                        of.getTerm(),
                        instanceBase,
                        ofBase,
                        used,
                        res);
                } else {
                    return false;
                }
            } else {
                return false;
            }
        } else if (!of.isQuestionMark() && !of.hasApplicableClause()) {
            in.addAll(of.getTerm().createSetOfAllNonAbstractVariables());
            return PrologAbstractState.calculateInstanceMatcher(
                instance.getTerm(),
                of.getTerm(),
                instanceBase,
                ofBase,
                used,
                res);
        } else {
            return false;
        }
    }

    /**
     * @param inst
     * @param of
     * @param ofBase
     * @param instBase
     * @param used
     * @param res
     * @return
     */
    private static boolean calculateInstanceMatcher(
        PrologTerm inst,
        PrologTerm of,
        KnowledgeBase instBase,
        KnowledgeBase ofBase,
        Set<PrologNonAbstractVariable> used,
        PrologSubstitution res
    ) {
        if (of.isVariable()) {
            if (res.containsKey(of)) {
                // we already checked this substitution part - it must just be equal
                return inst.equals(res.get(of));
            } else if (of.equals(inst)) {
                return !ofBase.isGround(of)
                    || instBase.isGround(inst)
                    && (!ofBase.isNumber(of) || instBase.isNumber(inst)
                        && ofBase.getIntegerMap().get(of).contains(instBase.getIntegerMap().get(inst)));
            } else if (of.isAbstractVariable()) {
                if (ofBase.isGround(of)
                    && (!instBase.isGround(inst) || ofBase.isNumber(of)
                        && (inst.isInt() && !ofBase.getIntegerMap().get(of).contains((PrologInt) inst) || !inst.isInt()
                            && (!inst.isAbstractVariable() || !instBase.isNumber(inst) || !ofBase
                                .getIntegerMap()
                                .get(of)
                                .contains(instBase.getIntegerMap().get(inst))))))
                {
                    return false;
                }
                res.put((PrologVariable) of, inst);
                return true;
            } else if (inst.isNonAbstractVariable() && !used.contains(inst)) {
                used.add((PrologNonAbstractVariable) inst);
                res.put((PrologVariable) of, inst);
                return true;
            } else {
                return false;
            }
        } else if (of.isCut()) {
            if (inst.isCut()) {
                if (of instanceof LabeledCut) {
                    if (inst instanceof LabeledCut) {
                        return ((LabeledCut) inst).getNumber() == ((LabeledCut) of).getNumber();
                    } else {
                        return false;
                    }
                } else {
                    return !(inst instanceof LabeledCut);
                }
            } else {
                return false;
            }
        } else if (!inst.isVariable() && of.createFunctionSymbol().equals(inst.createFunctionSymbol())) {
            for (int i = 0; i < of.getArity(); i++) {
                if (!PrologAbstractState.calculateInstanceMatcher(
                    inst.getArgument(i),
                    of.getArgument(i),
                    instBase,
                    ofBase,
                    used,
                    res))
                {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
    }

    /**
     * An abstract state A is an instance of another state B if there exists some substitution mu such that B\mu = A.
     * More on this idea can be found in Giesl et al.: Symbolic Evaluation Graphs and Term Rewriting.
     * @param instance Some abstract state. Must not be null.
     * @param of Some other abstract state that "instance" is suspected to be an instance of. Must not be null.
     * @param mu A substitution from of to instance. Must not be null.
     * @param used
     * @param in
     * @param noGroundLoss
     * @param aborter For abortions.
     * @return True if "instance" is an instance of "of" under the given substitution mu. False otherwise.
     */
    private static boolean checkInstanceMatcher(
        PrologAbstractState instance,
        PrologAbstractState of,
        PrologSubstitution mu,
        Set<PrologNonAbstractVariable> used,
        Set<PrologNonAbstractVariable> in,
        boolean noGroundLoss, Abortion aborter
    ) {
        final KnowledgeBase instKB = instance.getKnowledgeBase();
        final KnowledgeBase ofKB = of.getKnowledgeBase();
        final Set<PrologAbstractVariable> aIn = new LinkedHashSet<PrologAbstractVariable>();
        for (PrologVariable v : instance.createSetOfAllVariablesInState()) {
            if (v.isAbstractVariable()) {
                aIn.add((PrologAbstractVariable) v);
            }
        }
        for (PrologVariable v : of.createSetOfAllVariablesInState()) {
            if (v.isAbstractVariable()) {
                aIn.add((PrologAbstractVariable) v);
            }
        }
        // check that \mu|_\N is variable renaming
        used.retainAll(in);
        for (PrologNonAbstractVariable v : used) {
            if (!mu.containsKey(v)) {
                return false;
            }
        }
        // check U'\mu \subseteq U
        outerLoop: for (Pair<PrologTerm, PrologTerm> pair : ofKB.getNonUnifyingTerms()) {
            // apply \mu to terms
            final PrologTerm t1 = pair.x.applySubstitution(mu);
            final PrologTerm t2 = pair.y.applySubstitution(mu);
            // check if it is already in the instance's kb
            for (Pair<PrologTerm, PrologTerm> inPair : instKB.getNonUnifyingTerms()) {
                if ((inPair.x.equals(t1) && inPair.y.equals(t2)) || (inPair.x.equals(t2) && inPair.y.equals(t1))) {
                    continue outerLoop;
                }
            }
            // check for additional var renaming such that it is
            // in the instance's kb
            for (Pair<PrologTerm, PrologTerm> inPair : instKB.getNonUnifyingTerms()) {
                if (PrologAbstractState.isNonAbstractAndUnusedRenaming(t1, t2, inPair, in, aIn, mu)) {
                    continue outerLoop;
                }
            }
            return false;
        }
        final Set<PrologNonAbstractVariable> fPrimeMu = new LinkedHashSet<PrologNonAbstractVariable>();
        // check F'\mu \subseteq F
        for (PrologNonAbstractVariable v : ofKB.getFreeSet()) {
            PrologNonAbstractVariable toAdd = null;
            if (mu.containsKey(v)) {
                toAdd = (PrologNonAbstractVariable) mu.get(v);
                if (!instKB.isFree(toAdd)) {
                    return false;
                }
            } else {
                if (!instKB.isFree(v)) {
                    if (!in.contains(v)) {
                        final Set<PrologNonAbstractVariable> free =
                            new LinkedHashSet<PrologNonAbstractVariable>(instKB.getFreeSet());
                        free.removeAll(in);
                        if (!free.isEmpty()) {
                            mu.put(v, free.iterator().next());
                            toAdd = (PrologNonAbstractVariable) mu.get(v);
                        } else {
                            return false;
                        }
                    } else {
                        return false;
                    }
                } else {
                    toAdd = v;
                }
            }
            in.add(v);
            in.add(toAdd);
            fPrimeMu.add(toAdd);
        }
        // check F'\mu(Range(\mu|_A)) = \emptyset
        for (Map.Entry<PrologVariable, PrologTerm> entry : mu.entrySet()) {
            if (entry.getKey().isAbstractVariable()) {
                for (PrologNonAbstractVariable v : entry.getValue().createSetOfAllNonAbstractVariables()) {
                    if (fPrimeMu.contains(v)) {
                        return false;
                    }
                }
            }
        }
        // check forall a \in G' : V(a\mu) \subseteq G
        for (PrologAbstractVariable a : ofKB.getGroundSet()) {
            if (mu.containsKey(a)) {
                if (!instKB.isGround(mu.get(a))) {
                    return false;
                }
            } else if (!instKB.isGround(a)) {
                if (of.containsVariableInState(a) || instance.containsVariable(a) || aIn.contains(a)) {
                    return false;
                }
            }
        }
        // optional: check whether we lose ground information
        if (noGroundLoss) {
            for (Map.Entry<PrologVariable, PrologTerm> entry : mu.entrySet()) {
                if (instKB.isGround(entry.getValue()) && !ofKB.isGround(entry.getKey())) {
                    if (of.containsVariable(entry.getKey())) {
                        return false;
                    }
                }
            }
        }
        // check forall a \in I' : a\mu is an integer w.r.t. I and intervals are respected TODO more precise documentation
        for (Map.Entry<PrologAbstractVariable, PrologInterval> entry : ofKB.getIntegerMap().entrySet()) {
            PrologAbstractVariable a = entry.getKey();
            if (mu.containsKey(a)) {
                final PrologTerm t = mu.get(a);
                if (t.isInt()) {
                    if (!entry.getValue().contains((PrologInt) t)) {
                        return false;
                    }
                    continue;
                } else {
                    if (t.isAbstractVariable()) {
                        a = (PrologAbstractVariable) t;
                    } else {
                        return false;
                    }
                }
            }
            if (!instKB.isNumber(a) || !instKB.getIntegerMap().get(a).contains(entry.getValue())) {
                return false;
            }
        }
        // check instance relation of arithmetic states
        if (!instKB.isArithmeticInstanceOf(of, mu, aborter)) {
            return false;
        }
        return true;
    }

    private static boolean isNonAbstractAndUnusedRenaming(
        PrologSubstitution matcher1,
        PrologSubstitution matcher2,
        Set<PrologNonAbstractVariable> in,
        Set<PrologAbstractVariable> aIn,
        PrologSubstitution mu
    ) {
        final PrologSubstitution renaming = PrologSubstitution.isVariableRenaming(matcher1, matcher2);
        final Set<PrologNonAbstractVariable> nextIn = new LinkedHashSet<PrologNonAbstractVariable>();
        final Set<PrologAbstractVariable> nextAIn = new LinkedHashSet<PrologAbstractVariable>();
        boolean ok = true;
        if (renaming != null) {
            for (Map.Entry<PrologVariable, PrologTerm> entry : renaming.entrySet()) {
                final PrologVariable key = entry.getKey();
                final PrologVariable value = (PrologVariable) entry.getValue();
                if (
                    in.contains(key)
                    || in.contains(value)
                    || nextIn.contains(key)
                    || nextIn.contains(value)
                    || aIn.contains(key)
                    || aIn.contains(value)
                    || nextAIn.contains(key)
                    || nextAIn.contains(value)
                ) {
                    ok = false;
                    break;
                } else {
                    if (key.isAbstractVariable()) {
                        nextAIn.add((PrologAbstractVariable) key);
                        nextAIn.add((PrologAbstractVariable) value);
                    } else {
                        nextIn.add((PrologNonAbstractVariable) key);
                        nextIn.add((PrologNonAbstractVariable) value);
                    }
                }
            }
            if (ok) {
                for (Map.Entry<PrologVariable, PrologTerm> entry : renaming.entrySet()) {
                    mu.put(entry.getKey(), entry.getValue());
                }
                in.addAll(nextIn);
                aIn.addAll(nextAIn);
                return true;
            }
        }
        return false;
    }

    private static boolean isNonAbstractAndUnusedRenaming(
        PrologTerm t1,
        PrologTerm t2,
        Pair<PrologTerm, PrologTerm> pair,
        Set<PrologNonAbstractVariable> in,
        Set<PrologAbstractVariable> aIn,
        PrologSubstitution mu
    ) {
        return
            PrologAbstractState.isNonAbstractAndUnusedRenaming(
                t1.calculateMatcherWithAbstractVariables(pair.x),
                t2.calculateMatcherWithAbstractVariables(pair.y),
                in,
                aIn,
                mu
            )
            || PrologAbstractState.isNonAbstractAndUnusedRenaming(
                t1.calculateMatcherWithAbstractVariables(pair.y),
                t2.calculateMatcherWithAbstractVariables(pair.x),
                in,
                aIn,
                mu
            );
    }

    /**
     * The current goal.
     */
    private final ImmutableList<GoalElement> goal;

    /**
     * The knowledge base.
     */
    private final KnowledgeBase knowledgeBase;

    public PrologAbstractState(List<GoalElement> goalParam, KnowledgeBase kb) {
        this.goal = ImmutableCreator.create(goalParam);
        this.knowledgeBase = kb;
    }

    public Set<PrologVariable> createSetOfAllVariables() {
        Set<PrologVariable> res = this.createSetOfAllVariablesInState();
        res.addAll(this.getKnowledgeBase().getAllVars());
        return res;
    }

    public Set<PrologVariable> createSetOfAllVariablesInState() {
        Set<PrologVariable> vars = new LinkedHashSet<PrologVariable>();
        for (GoalElement e : this.getState()) {
            PrologTerm term = e.getTerm();
            if (term != null) {
                vars.addAll(term.createSetOfAllVariables());
            }
        }
        return vars;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof PrologAbstractState) {
            PrologAbstractState t = (PrologAbstractState) o;
            if (this.getState().size() != t.getState().size()) {
                return false;
            }
            for (int i = 0; i < this.getState().size(); i++) {
                if (!this.getState().get(i).equals(t.getState().get(i))) {
                    return false;
                }
            }
            return this.getKnowledgeBase().equals(t.getKnowledgeBase());
        }
        return false;
    }

    public GoalElement getHeadOfState() {
        return this.getState().size() == 0 ? null : this.getState().get(0);
    }

    /**
     * Returns the KnowledgeBase for this PartEvalTerm.
     * @return The KnowledgeBase for this PartEvalTerm.
     */
    public KnowledgeBase getKnowledgeBase() {
        return this.knowledgeBase;
    }

    public ImmutableList<GoalElement> getState() {
        return this.goal;
    }

    public List<GoalElement> getTailOfState() {
        List<GoalElement> res = new ArrayList<GoalElement>();
        for (int i = 1; i < this.getState().size(); i++) {
            res.add(this.getState().get(i));
        }
        return res;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.getState().hashCode() + this.getKnowledgeBase().hashCode() + 3;
    }

    public boolean isEmpty() {
        return this.getState().isEmpty();
    }

    @Override
    public String prettyToString() {
        StringBuilder res = new StringBuilder();
        boolean first = true;
        for (GoalElement s : this.getState()) {
            if (first) {
                res.append(s.prettyToString());
                first = false;
            } else {
                res.append(" | ");
                res.append(s.prettyToString());
            }
        }
        res.append("\\n\\n");
        res.append(this.getKnowledgeBase().prettyToString());
        return res.toString();
    }

    /**
     * Sets the KnowledgeBase.
     * @param base The KnowledgeBase to set.
     */
    public PrologAbstractState replaceKnowledgeBase(KnowledgeBase base) {
        return new PrologAbstractState(this.getState(), base);
    }

    public PrologAbstractState replaceState(List<GoalElement> state) {
        return new PrologAbstractState(state, this.getKnowledgeBase());
    }

    /**
     * @param t
     */
    public PrologAbstractState replaceState(PrologTerm t) {
        return PrologAbstractState.createFromTerm(t, this.getKnowledgeBase());
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("goal", JSONExportUtil.toJSON(this.goal));
        res.put("kb", JSONExportUtil.toJSON(this.knowledgeBase));
        return res;
    }

    public String toLaTeX() {
        if (this.isEmpty()) {
            return "\\varepsilon";
        }
        StringBuilder res = new StringBuilder();
        res.append(this.getHeadOfState().toLaTeX(this.getKnowledgeBase()));
        for (GoalElement e : this.getTailOfState()) {
            res.append(" \\mid ");
            res.append(e.toLaTeX(this.getKnowledgeBase()));
        }
        return res.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        boolean first = true;
        for (GoalElement s : this.getState()) {
            if (first) {
                res.append(s.toString());
                first = false;
            } else {
                res.append(" | ");
                res.append(s.toString());
            }
        }
        res.append("\n\n");
        res.append(this.getKnowledgeBase().toString());
        return res.toString();
    }

    private boolean containsVariable(PrologVariable v) {
        return this.containsVariableInState(v) || this.getKnowledgeBase().getAllVars().contains(v);
    }

    private boolean containsVariableInState(PrologVariable v) {
        for (GoalElement e : this.getState()) {
            if (!e.isQuestionMark()) {
                if (e.getTerm().createSetOfAllVariables().contains(v)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static class ErrorState extends PrologAbstractState {

        public ErrorState(SMTSolverFactory factory, SMTLIBLogic logic) {
            super(new LinkedList<GoalElement>(), KnowledgeBase.createEmpty(factory, logic));
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof ErrorState;
        }

        @Override
        public String toString() {
            return "AbstractErrorState";
        }

    }

}
