package aprove.input.Programs.prolog.graph;

import java.util.*;

import org.json.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * A KnowledgeBase contains information about the abstract variables in an abstract state.<br><br>
 *
 * Created: Dec 4, 2006<br>
 * Last modified: Aug 18, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public class KnowledgeBase implements PrettyStringable, Immutable, JSONExport {

    /**
     * Constructs a KnowledgeBase with the specified information.
     * @param g A set containing those abstract variables
     *          considered to be ground.
     * @param f A set containing those nonabstract variables
     *          considered to be free.
     * @param u A set of pairs of PrologTerms considered not to
     *          unify.
     * @param n A map from those abstract variables considered to only represent integer numbers to the corresponding
     *          interval specifying which integers the respective variable represents.
     * @param factory
     */
    public static KnowledgeBase create(
        Set<PrologAbstractVariable> g,
        Set<PrologNonAbstractVariable> f,
        Set<Pair<PrologTerm, PrologTerm>> u,
        Map<PrologAbstractVariable, PrologInterval> n,
        SMTSolverFactory factory,
        SMTLIBLogic logic
    ) {
        Set<PrologAbstractVariable> newGround = new LinkedHashSet<PrologAbstractVariable>(g);
        newGround.addAll(n.keySet());
        final PrologToIntegerConverter converter = PrologToIntegerConverter.create();
        return
            new KnowledgeBase(
                newGround,
                f,
                u,
                new LinkedHashSet<PrologAbstractVariable>(),
                n,
                SafeEvaluationHeuristic.create(converter),
                converter,
                new PlainIntegerRelationState(factory, logic)
            );
    }

    /**
     * @param ground The ground vars.
     * @param free The free vars.
     * @param nonunify The nonunifying terms.
     * @param numbers The integer numbers.
     * @return
     */
    public static KnowledgeBase createCleanedKnowledgeBase(
        Set<PrologAbstractVariable> ground,
        Set<PrologNonAbstractVariable> free,
        Set<Pair<PrologTerm, PrologTerm>> nonunify,
        Set<PrologAbstractVariable> expressionVars,
        Map<PrologAbstractVariable, PrologInterval> numbers,
        IntegerState arithmeticState
    ) {
        Set<Pair<PrologTerm, PrologTerm>> toDel = new LinkedHashSet<Pair<PrologTerm, PrologTerm>>();
        // first remove all pairs without an mgu
        for (Pair<PrologTerm, PrologTerm> pair : nonunify) {
            if (pair.x.calculateMGU(pair.y) == null) {
                toDel.add(pair);
            }
        }
        nonunify.removeAll(toDel);
        // then only keep pairs modulo non-abstract variable renaming
        // where the renaming also respects knowledge about free variables
        final Set<Pair<PrologTerm, PrologTerm>> newNonunify = new LinkedHashSet<Pair<PrologTerm, PrologTerm>>();
        for (Pair<PrologTerm, PrologTerm> candidate : nonunify) {
            boolean in = true;
            for (Pair<PrologTerm, PrologTerm> representative : newNonunify) {
                PrologSubstitution matcher1 = candidate.x.calculateMatcher(representative.x);
                PrologSubstitution matcher2 = candidate.y.calculateMatcher(representative.y);
                PrologSubstitution renaming = PrologSubstitution.isNonAbstractRenaming(matcher1, matcher2);
                if (renaming != null) {
                    final Set<PrologNonAbstractVariable> checkedVars = new LinkedHashSet<PrologNonAbstractVariable>();
                    for (Map.Entry<PrologVariable, PrologTerm> entry : renaming.entrySet()) {
                        final PrologNonAbstractVariable key = (PrologNonAbstractVariable) entry.getKey();
                        final PrologNonAbstractVariable value = (PrologNonAbstractVariable) entry.getValue();
                        if ((free.contains(key) && !free.contains(value))
                            || (!free.contains(key) && free.contains(value))
                            || checkedVars.contains(key)
                            || checkedVars.contains(value))
                        {
                            in = false;
                            break;
                        } else {
                            checkedVars.add(key);
                            checkedVars.add(value);
                        }
                    }
                }
                if (in) {
                    matcher1 = candidate.x.calculateMatcher(representative.y);
                    matcher2 = candidate.y.calculateMatcher(representative.x);
                    renaming = PrologSubstitution.isNonAbstractRenaming(matcher1, matcher2);
                    if (renaming != null) {
                        final Set<PrologNonAbstractVariable> checkedVars =
                            new LinkedHashSet<PrologNonAbstractVariable>();
                        for (Map.Entry<PrologVariable, PrologTerm> entry : renaming.entrySet()) {
                            final PrologNonAbstractVariable key = (PrologNonAbstractVariable) entry.getKey();
                            final PrologNonAbstractVariable value = (PrologNonAbstractVariable) entry.getValue();
                            if ((free.contains(key) && !free.contains(value))
                                || (!free.contains(key) && free.contains(value))
                                || checkedVars.contains(key)
                                || checkedVars.contains(value))
                            {
                                in = false;
                                break;
                            } else {
                                checkedVars.add(key);
                                checkedVars.add(value);
                            }
                        }
                    }
                    if (!in) {
                        break;
                    }
                } else {
                    break;
                }
            }
            if (in) {
                newNonunify.add(candidate);
            }
        }
        // ensure that all numbers are known to be ground
        final Set<PrologAbstractVariable> newGround = new LinkedHashSet<PrologAbstractVariable>(ground);
        newGround.addAll(numbers.keySet());
        final PrologToIntegerConverter converter = PrologToIntegerConverter.create();
        return
            new KnowledgeBase(
                newGround,
                free,
                newNonunify,
                expressionVars,
                numbers,
                SafeEvaluationHeuristic.create(converter),
                converter,
                arithmeticState
            );
    }

    /**
     * Constructs an empty KnowledgeBase.
     * @param factory Factory to build SMT solvers.
     */
    public static KnowledgeBase createEmpty(SMTSolverFactory factory, SMTLIBLogic logic) {
        final PrologToIntegerConverter converter = PrologToIntegerConverter.create();
        return
            new KnowledgeBase(
                new LinkedHashSet<PrologAbstractVariable>(),
                new LinkedHashSet<PrologNonAbstractVariable>(),
                new LinkedHashSet<Pair<PrologTerm, PrologTerm>>(),
                new LinkedHashSet<PrologAbstractVariable>(),
                new LinkedHashMap<PrologAbstractVariable, PrologInterval>(),
                SafeEvaluationHeuristic.create(converter),
                converter,
                new PlainIntegerRelationState(factory, logic)
            );
    }

    /**
     * Constructs a KnowledgeBase with the given set of ground variables and the given mapping of variables to intervals
     * @param g A set containing those abstract variables
     *          considered to be ground.
     * @param n A map from those abstract variables considered to only represent integer numbers to the corresponding
     *          interval specifying which integers the respective variable represents.
     * @param factory Factory to build SMT solvers.
     */
    public static KnowledgeBase createWithGroundAndIntegers(
        Set<PrologAbstractVariable> g,
        Map<PrologAbstractVariable, PrologInterval> n,
        SMTSolverFactory factory,
        SMTLIBLogic logic
    ) {
        final Set<PrologAbstractVariable> newGround = new HashSet<>(g);
        newGround.addAll(n.keySet());
        final PrologToIntegerConverter converter = PrologToIntegerConverter.create();
        return
            new KnowledgeBase(
                newGround,
                new LinkedHashSet<PrologNonAbstractVariable>(),
                new LinkedHashSet<Pair<PrologTerm, PrologTerm>>(),
                new LinkedHashSet<PrologAbstractVariable>(),
                n,
                SafeEvaluationHeuristic.create(converter),
                converter,
                new PlainIntegerRelationState(factory, logic)
            );
    }

    /**
     * Constructs a KnowledgeBase with the given ground information.
     * @param g A set containing those abstract variables
     *          considered to be ground.
     * @param factory Factory to build SMT solvers.
     */
    public static KnowledgeBase createWithGroundVars(
        Set<PrologAbstractVariable> g,
        SMTSolverFactory factory,
        SMTLIBLogic logic
    ) {
        final PrologToIntegerConverter converter = PrologToIntegerConverter.create();
        return
            new KnowledgeBase(
                g,
                new LinkedHashSet<PrologNonAbstractVariable>(),
                new LinkedHashSet<Pair<PrologTerm, PrologTerm>>(),
                new LinkedHashSet<PrologAbstractVariable>(),
                new LinkedHashMap<PrologAbstractVariable, PrologInterval>(),
                SafeEvaluationHeuristic.create(converter),
                converter,
                new PlainIntegerRelationState(factory, logic)
            );
    }

    private static boolean computeVarRenaming(
        PrologTerm t1,
        PrologTerm t2,
        PrologSubstitution renaming
    ) {
        if (t1.isVariable()) {
            if (t2.isVariable()) {
                if (t1.equals(t2)) {
                    return true;
                } else if (renaming.containsKey(t1)) {
                    return renaming.get(t1).equals(t2);
                } else if (renaming.containsKey(t2)) {
                    return renaming.get(t2).equals(t1);
                } else {
                    renaming.put((PrologVariable) t1, t2);
                    return true;
                }
            } else {
                return false;
            }
        } else if (t2.isVariable()) {
            return false;
        } else if (t1.createFunctionSymbol().equals(t2.createFunctionSymbol())) {
            for (int i = 0; i < t1.getArity(); i++) {
                if (!KnowledgeBase.computeVarRenaming(t1.getArgument(i), t2.getArgument(i), renaming)) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
    }

    private static boolean containsNoVars(PrologSubstitution renaming, VariableSet vars) {
        // we expect to get a variable renaming
        for (Map.Entry<PrologVariable, PrologTerm> entry : renaming.entrySet()) {
            if (vars.contains(entry.getKey()) || vars.contains(entry.getValue())) {
                return false;
            }
        }
        return true;
    }

    private static boolean equivalentInfo(
        Pair<PrologTerm, PrologTerm> pair1,
        Pair<PrologTerm, PrologTerm> pair2,
        VariableSet vars
    ) {
        return
            KnowledgeBase.equivalentInfo(pair1.x, pair1.y, pair2.x, pair2.y, vars)
            || KnowledgeBase.equivalentInfo(pair1.x, pair1.y, pair2.y, pair2.x, vars);
    }

    private static boolean equivalentInfo(
        PrologTerm x1,
        PrologTerm y1,
        PrologTerm x2,
        PrologTerm y2,
        VariableSet vars
    ) {
        PrologSubstitution renaming = new PrologSubstitution();
        if (KnowledgeBase.computeVarRenaming(x1, x2, renaming)) {
            if (KnowledgeBase.computeVarRenaming(y1, y2, renaming)) {
                return KnowledgeBase.containsNoVars(renaming, vars);
            } else {
                return false;
            }
        } else {
            return false;
        }
    }

    /**
     * Represents the arithmetic state of this knowledge base
     */
    private final IntegerState arithmeticState;

    /**
     * The variables which are known to represent an integer expression, maybe with non abstract variables
     */
    private final ImmutableSet<PrologAbstractVariable> expressionVars;

    /**
     * The nonabstract variables not occurring in terms represented by abstract variables.
     */
    private final ImmutableSet<PrologNonAbstractVariable> freeVars;

    /**
     * The abstract variables only representing ground terms.
     */
    private final ImmutableSet<PrologAbstractVariable> groundVars;

    //TODO check this class for numberVars usage

    /**
     * The abstract variables only representing integer numbers from their corresponding interval. Its keySet must be a
     * subset of groundVars.
     */
    private final Map<PrologAbstractVariable, PrologInterval> integerVars;

    /**
     * The pairs of terms which must not unify after concretizing all abstract variables.
     */
    private final ImmutableSet<Pair<PrologTerm, PrologTerm>> nonunifyingTerms;

    /**
     * Heuristic used for checking whether or not we will run into exceptions when evaluating a given prolog term
     */
    private final SafeEvaluationHeuristic safeEvaluationHeuristic;

    /**
     * Converter used to convert terms that represent arithmetic relations to that data type
     */
    private final PrologToIntegerConverter termToRelationConverter;

    /**
     * Constructs a KnowledgeBase with the specified information.
     * @param g A set containing those abstract variables
     *          considered to be ground.
     * @param f A set containing those nonabstract variables
     *          considered to be free.
     * @param e A set containing those abstract variables considered
     *             to represent an integer expression with variables
     * @param u A set of pairs of PrologTerms considered not to
     *          unify.
     * @param n A map from those abstract variables considered to only represent integer numbers to the corresponding
     *          interval specifying which integers the respective variable represents.
     */
    protected KnowledgeBase(
        Set<PrologAbstractVariable> g,
        Set<PrologNonAbstractVariable> f,
        Set<Pair<PrologTerm, PrologTerm>> u,
        Set<PrologAbstractVariable> e,
        Map<PrologAbstractVariable, PrologInterval> n,
        SafeEvaluationHeuristic safeEvaluationHeuristic,
        PrologToIntegerConverter termToRelationConverter,
        IntegerState arithmeticState
    ) {
        this.groundVars = ImmutableCreator.create(g);
        this.freeVars = ImmutableCreator.create(f);
        this.nonunifyingTerms = ImmutableCreator.create(u);
        this.expressionVars = ImmutableCreator.create(e);
        this.integerVars = ImmutableCreator.create(n);
        assert this.groundVars.containsAll(this.integerVars.keySet()) : "Invariant violated";
        this.safeEvaluationHeuristic = safeEvaluationHeuristic;
        this.termToRelationConverter = termToRelationConverter;
        this.arithmeticState = arithmeticState;
    }

    public KnowledgeBase addFreeVariables(Collection<? extends PrologNonAbstractVariable> vars) {
        Set<PrologNonAbstractVariable> free = new LinkedHashSet<PrologNonAbstractVariable>(this.getFreeSet());
        free.addAll(vars);
        return
            new KnowledgeBase(
                this.getGroundSet(),
                free,
                this.getNonUnifyingTerms(),
                this.expressionVars,
                this.getIntegerMap(),
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                this.arithmeticState
            );
    }

    public KnowledgeBase addGroundVariables(Collection<? extends PrologAbstractVariable> vars) {
        Set<PrologAbstractVariable> ground = new LinkedHashSet<PrologAbstractVariable>(this.getGroundSet());
        ground.addAll(vars);
        return
            new KnowledgeBase(
                ground,
                this.getFreeSet(),
                this.getNonUnifyingTerms(),
                this.expressionVars,
                this.getIntegerMap(),
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                this.arithmeticState
            );
    }

    public KnowledgeBase assumeArithCompFalse(PrologTerm term, Abortion aborter) {
        final Set<PrologAbstractVariable> termVariables = term.createSetOfAllAbstractVariables();
        final Set<PrologAbstractVariable> newGroundVariables = new HashSet<PrologAbstractVariable>(this.groundVars);
        newGroundVariables.addAll(termVariables);
        final Set<PrologAbstractVariable> newExpressionVariables =
             new HashSet<PrologAbstractVariable>(this.expressionVars);
        newExpressionVariables.addAll(termVariables);
        final IntegerRelation relation = this.termToRelationConverter.convertRelation(term);
        final IntegerState newArithmeticState = this.arithmeticState.addRelation(relation.negate(), aborter);
        return
            new KnowledgeBase(
                newGroundVariables,
                this.freeVars,
                this.nonunifyingTerms,
                newExpressionVariables,
                this.integerVars,
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                newArithmeticState
            );
    }

    public KnowledgeBase assumeArithCompTrue(PrologTerm term, Abortion aborter) {
        final Set<PrologAbstractVariable> termVariables = term.createSetOfAllAbstractVariables();
        final Set<PrologAbstractVariable> newGroundVariables = new HashSet<>(this.groundVars);
        newGroundVariables.addAll(termVariables);
        final Set<PrologAbstractVariable> newExpressionVariables = new HashSet<>(this.expressionVars);
        newExpressionVariables.addAll(termVariables);
        final IntegerRelation relation = this.termToRelationConverter.convertRelation(term);
        final IntegerState newArithmeticState = this.arithmeticState.addRelation(relation, aborter);
        return
            new KnowledgeBase(
                newGroundVariables,
                this.freeVars,
                this.nonunifyingTerms,
                newExpressionVariables,
                this.integerVars,
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                newArithmeticState
            );
    }

    public KnowledgeBase assumeSafeEvaluation(PrologTerm expr) {
        final Set<PrologAbstractVariable> exprVars = expr.createSetOfAllAbstractVariables();
        final Set<PrologAbstractVariable> newExpressionVars = new HashSet<>(this.expressionVars);
        newExpressionVars.addAll(exprVars);
        final Set<PrologAbstractVariable> newGroundVars = new HashSet<>(this.groundVars);
        newGroundVars.addAll(exprVars);
        return
            new KnowledgeBase(
                newGroundVars,
                this.freeVars,
                this.nonunifyingTerms,
                newExpressionVars,
                this.integerVars,
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                this.arithmeticState
            );
    }

    public KnowledgeBase assumeUnificationFail(PrologTerm target, PrologTerm expr) {
        Set<Pair<PrologTerm, PrologTerm>> newNonunifyingTerms = new HashSet<>(this.nonunifyingTerms);
        newNonunifyingTerms.add(new Pair<>(target, expr));
        return
            new KnowledgeBase(
                this.groundVars,
                this.freeVars,
                newNonunifyingTerms,
                this.expressionVars,
                this.integerVars,
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                this.arithmeticState
            );
    }

    /**
     * @param t Some term, which must be a arithmetic comparison.
     * @param aborter For abortions.
     * @return True, if we know that the comparison is true. False otherwise.
     */
    public boolean checkArithComp(PrologTerm t, Abortion aborter) {
        return this.arithmeticState.checkRelation(this.termToRelationConverter.convertRelation(t), aborter).x;
    }

    /**
     * @param t Some term, which must be a arithmetic comparison.
     * @param aborter For abortions.
     * @return True, if we know that the comparison is false. False otherwise.
     */
    public boolean checkArithCompInverse(PrologTerm t, Abortion aborter) {
        return this.arithmeticState.checkRelation(this.termToRelationConverter.convertRelation(t).negate(), aborter).x;
    }

    public Pair<PrologTerm, PrologTerm> computePossibleClash(PrologSubstitution sigma) {
        if (sigma != null) {
            final PrologSubstitution sigmaG = sigma.restrict(this.getGroundSet());
            outerLoop: for (Pair<PrologTerm, PrologTerm> pair : this.getNonUnifyingTerms()) {
                final PrologTerm s1 = pair.x.applySubstitution(sigmaG);
                final PrologTerm s2 = pair.y.applySubstitution(sigmaG);
                final PrologSubstitution sigmaPrime = s1.calculateMGU(s2);
                if (sigmaPrime != null) {
                    for (Map.Entry<PrologVariable, PrologTerm> entry : sigmaPrime.entrySet()) {
                        if (entry.getKey().isAbstractVariable()) {
                            continue outerLoop;
                        }
                    }
                    return pair;
                }
            }
            final PrologSubstitution sigmaI = sigma.restrict(this.getIntegerSet());
            for (Map.Entry<PrologVariable, PrologTerm> entry : sigmaI.entrySet()) {
                final PrologVariable key = entry.getKey();
                final PrologTerm value = entry.getValue();
                if (
                    (!value.isInt() && !value.isAbstractVariable())
                    || (
                        value.isAbstractVariable()
                        && this.isNumber(value)
                        && this.getIntegerMap().get(key).hasEmptyIntersection(this.getIntegerMap().get(value))
                    )
                    || (
                        !value.isAbstractVariable()
                        && value.isInt()
                        && this.getIntegerMap().get(key).contains((PrologInt)value)
                    )
                ) {
                    return new Pair<PrologTerm, PrologTerm>(key, value);
                }
            }
        }
        return null;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof KnowledgeBase) {
            KnowledgeBase inst = (KnowledgeBase) o;
            return this.hashCode() == inst.hashCode()
                && this.getGroundSet().equals(inst.getGroundSet())
                && this.getFreeSet().equals(inst.getFreeSet())
                && this.getNonUnifyingTerms().equals(inst.getNonUnifyingTerms())
                && this.getIntegerMap().equals(inst.getIntegerMap());
        }
        return false;
    }

    /**
     * @return
     */
    public VariableSet getAllVars() {
        VariableSet res = new VariableSet();
        res.addAll(this.getFreeSet());
        res.addAll(this.getGroundSet());
        for (Pair<PrologTerm, PrologTerm> pair : this.getNonUnifyingTerms()) {
            res.addAll(pair.x.createSetOfAllVariables());
            res.addAll(pair.y.createSetOfAllVariables());
        }
        //res.addAll(this.getNumberMap().keySet()); not necessary since the keySet is a subset of the groundSet
        return res;
    }

    public ImmutableSet<PrologNonAbstractVariable> getFreeSet() {
        return this.freeVars;
    }

    public ImmutableSet<PrologAbstractVariable> getGroundSet() {
        return this.groundVars;
    }

    /**
     * @return The map from abstract variables only representing integer numbers to their corresponding intervals.
     */
    public Map<PrologAbstractVariable, PrologInterval> getIntegerMap() {
        return this.integerVars;
    }

    public Set<PrologAbstractVariable> getIntegerSet() {
        return this.getIntegerMap().keySet();
    }

    public ImmutableSet<Pair<PrologTerm, PrologTerm>> getNonUnifyingTerms() {
        return this.nonunifyingTerms;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return
            23 * (
                this.getGroundSet().hashCode()
                + this.getFreeSet().hashCode()
                + this.getNonUnifyingTerms().hashCode()
                + this.getIntegerMap().hashCode()
            );
    }

    public boolean hasOnlyFreeNonAbstractVariables(PrologTerm t) {
        if (t.isNonAbstractVariable()) {
            return this.isFree((PrologNonAbstractVariable) t);
        } else {
            for (PrologTerm child : t.getArguments()) {
                if (!this.hasOnlyFreeNonAbstractVariables(child)) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * A state A is an arithmetic instance of state B under some relation mu if for all relations r in B's arithmetic
     * state it holds that A's arithmetic state implies r\mu. More formally, A is an arithmetic instance of B under mu
     * if forall r in B: A |= r\mu.
     * @param of Some abstract state. Must not be null.
     * @param mu Some substitution. Must not be null.
     * @param aborter For abortions.
     * @return True if this is an instance of of under mu. False otherwise.
     */
    public boolean isArithmeticInstanceOf(PrologAbstractState of, PrologSubstitution mu, Abortion aborter) {
        assert of != null;
        assert mu != null;
        final KnowledgeBase ofKb = of.getKnowledgeBase();
        final Map<IntegerVariable, FunctionalIntegerExpression> substitution =
            this.termToRelationConverter.convertSubstitution(mu);
        IntegerState interfaceWithSubstitution = this.arithmeticState;
        for (Map.Entry<PrologVariable, PrologTerm> substitutionEntry : mu.entrySet()) {
            final IntegerRelation relation =
                this.termToRelationConverter.convertRelation(
                    PrologTerm.create("=:=", substitutionEntry.getKey(), substitutionEntry.getValue())
                );
            if (relation != null) {
                interfaceWithSubstitution = interfaceWithSubstitution.addRelation(relation, aborter);
            }
        }
        for (IntegerRelation ofRelation : ofKb.arithmeticState.toRelationSet()) {
            final IntegerRelation ofRelationMu = ofRelation.applySubstitution(substitution);
            if (!interfaceWithSubstitution.checkRelation(ofRelationMu, aborter).x) {
                return false;
            }
        }
        return true;
    }

    public boolean isEmpty() {
        return this.getGroundSet().isEmpty() && this.getFreeSet().isEmpty() && this.getNonUnifyingTerms().isEmpty();
        //&& this.getNumberMap().isEmpty(); not necessary since its keySet is a subset of the groundSet.
    }

    public boolean isFree(PrologNonAbstractVariable v) {
        return this.getFreeSet().contains(v);
    }

    public boolean isGround(PrologTerm term) {
        if (term.isAbstractVariable()) {
            return this.getGroundSet().contains(term);
            //no check for number needed since all numbers must be ground terms
        } else if (term.isVariable()) {
            return false;
        } else {
            boolean res = true;
            for (PrologTerm child : term.getArguments()) {
                res &= this.isGround(child);
            }
            return res;
        }
    }

    /**
     * @param t The term to check for being an integer.
     * @return True if we know that the specified term only represents integer numbers.
     */
    public boolean isNumber(PrologTerm t) {
        if (t.isAbstractVariable()) {
            return this.getIntegerMap().containsKey(t);
        }
        return t.isInt();
    }

    /**
     * The conditions under which arithmetic evaluation of a term throws an exception are detailed in Deransart et al.,
     * Prolog - The Standard: Reference Manual, section 6.2
     * @param t Some term, must not be null.
     * @param aborter For abortions.
     * @return YES, if arithmetic evaluation of this term does not throw an exception. NO if it does throw an
     *         exception. MAYBE if both cases are possible.
     */
    public YNM isSafe(PrologTerm t, Abortion aborter) {
        Set<PrologAbstractVariable> groundExpressionVars = new HashSet<>(this.groundVars);
        groundExpressionVars.retainAll(this.expressionVars);
        return this.safeEvaluationHeuristic.isSafe(groundExpressionVars, this.arithmeticState, t, aborter);
    }

    /**
     * @return
     */
    @Override
    public String prettyToString() {
        StringBuilder res = new StringBuilder();
        boolean first = true;
        for (PrologAbstractVariable t : this.getGroundSet()) {
            if (first) {
                first = false;
            } else {
                res.append("\\n");
            }
            res.append(t.prettyToString());
            res.append(" is ground");
        }
        for (PrologNonAbstractVariable t : this.getFreeSet()) {
            if (first) {
                first = false;
            } else {
                res.append("\\n");
            }
            res.append(t.prettyToString());
            res.append(" is free");
        }
        for (Pair<PrologTerm, PrologTerm> pair : this.getNonUnifyingTerms()) {
            if (first) {
                first = false;
            } else {
                res.append("\\n");
            }
            res.append(pair.x.prettyToString());
            res.append(" !=? ");
            res.append(pair.y.prettyToString());
        }
        for (Map.Entry<PrologAbstractVariable, PrologInterval> entry : this.getIntegerMap().entrySet()) {
            if (first) {
                first = false;
            } else {
                res.append("\\n");
            }
            res.append(entry.getKey().prettyToString());
            res.append(" in ");
            res.append(entry.getValue().toString());
        }
        res.append(this.arithmeticState.toString());
        return res.toString();
    }

    /**
     * @param state
     */
    public KnowledgeBase reduceToState(List<GoalElement> state) {
        VariableSet vars = new VariableSet();
        for (GoalElement e : state) {
            if (!e.isQuestionMark()) {
                vars.addAll(e.getTerm().createSetOfAllVariables());
            }
        }
        return this.reduceToVars(vars);
    }

    public KnowledgeBase reduceToVars(Set<? extends PrologVariable> vars) {
        return this.reduceToVars(new VariableSet(vars));
    }

    public KnowledgeBase reduceToVars(VariableSet vars) {
        final VariableSet aVars = vars.restrictToAbstractVariables(), cVars = vars.copy();
        final Set<Pair<PrologTerm, PrologTerm>> nonunify = new LinkedHashSet<Pair<PrologTerm, PrologTerm>>();
        outerLoop: for (Pair<PrologTerm, PrologTerm> pair : this.getNonUnifyingTerms()) {
            final VariableSet set = pair.x.createSetOfAllVariables();
            set.addAll(pair.y.createSetOfAllVariables());
            if (!set.disjoint(aVars)) {
                final PrologSubstitution mgu = pair.x.calculateMGU(pair.y);
                if (mgu != null) {
                    for (Pair<PrologTerm, PrologTerm> alreadyIn : nonunify) {
                        if (KnowledgeBase.equivalentInfo(alreadyIn, pair, vars)) {
                            continue outerLoop;
                        }
                    } // we do not already have equivalent info
                    nonunify.add(pair);
                    cVars.addAll(set);
                }
            }
        }
        final Set<PrologAbstractVariable> ground = new LinkedHashSet<PrologAbstractVariable>(this.getGroundSet());
        final Set<PrologNonAbstractVariable> free = new LinkedHashSet<PrologNonAbstractVariable>(this.getFreeSet());
        final Map<PrologAbstractVariable, PrologInterval> numbers =
            new LinkedHashMap<PrologAbstractVariable, PrologInterval>(this.getIntegerMap());
        ground.retainAll(cVars);
        free.retainAll(cVars);
        final Iterator<PrologAbstractVariable> iterator = numbers.keySet().iterator();
        while (iterator.hasNext()) {
            if (!cVars.contains(iterator.next())) {
                iterator.remove();
            }
        }
        // TODO: Restrict expression vars and arithmeticState to given set of variables
        return
            KnowledgeBase.createCleanedKnowledgeBase(
                ground,
                free,
                nonunify,
                this.expressionVars,
                numbers,
                this.arithmeticState
            );
    }

    /**
     * @param v
     * @param b
     */
    public KnowledgeBase setFree(PrologNonAbstractVariable v, boolean b) {
        Set<PrologNonAbstractVariable> free = new LinkedHashSet<PrologNonAbstractVariable>(this.getFreeSet());
        if (b) {
            free.add(v);
        } else {
            free.remove(v);
        }
        return
            new KnowledgeBase(
                this.getGroundSet(),
                free,
                this.getNonUnifyingTerms(),
                this.expressionVars,
                this.getIntegerMap(),
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                this.arithmeticState
            );
    }

    public KnowledgeBase setGround(PrologAbstractVariable t, boolean b) {
        Set<PrologAbstractVariable> ground = new LinkedHashSet<PrologAbstractVariable>(this.getGroundSet());
        if (b) {
            ground.add(t);
        } else {
            ground.remove(t);
            if (this.isNumber(t)) {
                Map<PrologAbstractVariable, PrologInterval> numbers =
                    new LinkedHashMap<PrologAbstractVariable, PrologInterval>(this.getIntegerMap());
                numbers.remove(t);
                return
                    new KnowledgeBase(
                        ground,
                        this.getFreeSet(),
                        this.getNonUnifyingTerms(),
                        this.expressionVars,
                        numbers,
                        this.safeEvaluationHeuristic,
                        this.termToRelationConverter,
                        this.arithmeticState
                    );
            }
        }
        return
            new KnowledgeBase(
                ground,
                this.getFreeSet(),
                this.getNonUnifyingTerms(),
                this.expressionVars,
                this.getIntegerMap(),
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                this.arithmeticState
            );
    }

    /**
     * @param x
     * @param y
     */
    public KnowledgeBase setNonUnify(PrologTerm x, PrologTerm y) {
        Set<Pair<PrologTerm, PrologTerm>> nonunify =
            new LinkedHashSet<Pair<PrologTerm, PrologTerm>>(this.getNonUnifyingTerms());
        nonunify.add(new Pair<PrologTerm, PrologTerm>(x, y));
        return
            KnowledgeBase.createCleanedKnowledgeBase(
                this.getGroundSet(),
                this.getFreeSet(),
                nonunify,
                this.expressionVars,
                this.getIntegerMap(),
                this.arithmeticState
            );
    }

    public KnowledgeBase setNumber(PrologAbstractVariable var, PrologInterval i) {
        Map<PrologAbstractVariable, PrologInterval> numbers =
            new LinkedHashMap<PrologAbstractVariable, PrologInterval>(this.getIntegerMap());
        numbers.put(var, i);
        return
            KnowledgeBase.createCleanedKnowledgeBase(
                this.getGroundSet(),
                this.getFreeSet(),
                this.getNonUnifyingTerms(),
                this.expressionVars,
                numbers,
                this.arithmeticState
            );
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("ground", JSONExportUtil.toJSON(this.groundVars));
        res.put("free", JSONExportUtil.toJSON(this.freeVars));
        res.put("nonunifying", JSONExportUtil.toJSON(this.nonunifyingTerms));
        res.put("intvars", JSONExportUtil.toJSON(this.integerVars));
        res.put("exprvars", JSONExportUtil.toJSON(this.expressionVars));
        res.put("arithmetic", JSONExportUtil.toJSON(this.arithmeticState));
        return res;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        boolean first = true;
        for (PrologAbstractVariable t : this.getGroundSet()) {
            if (first) {
                first = false;
            } else {
                res.append("\n");
            }
            res.append(t.toString());
            res.append(" is ground");
        }
        for (PrologNonAbstractVariable t : this.getFreeSet()) {
            if (first) {
                first = false;
            } else {
                res.append("\n");
            }
            res.append(t.toString());
            res.append(" is free");
        }
        for (Pair<PrologTerm, PrologTerm> pair : this.getNonUnifyingTerms()) {
            if (first) {
                first = false;
            } else {
                res.append("\n");
            }
            res.append(pair.x.toString());
            res.append(" !=? ");
            res.append(pair.y.toString());
        }
        for (Map.Entry<PrologAbstractVariable, PrologInterval> entry : this.getIntegerMap().entrySet()) {
            if (first) {
                first = false;
            } else {
                res.append("\\n");
            }
            res.append(entry.getKey().prettyToString());
            res.append(" in ");
            res.append(entry.getValue().toString());
        }
        return res.toString();
    }

    /**
     * @param information
     * @throws InconsistencyException
     */
    public KnowledgeBase union(KnowledgeBase information) {
        final Set<PrologAbstractVariable> ground = new LinkedHashSet<PrologAbstractVariable>(this.getGroundSet());
        final Set<PrologNonAbstractVariable> free = new LinkedHashSet<PrologNonAbstractVariable>(this.getFreeSet());
        final Set<Pair<PrologTerm, PrologTerm>> nonunify =
            new LinkedHashSet<Pair<PrologTerm, PrologTerm>>(this.getNonUnifyingTerms());
        final Map<PrologAbstractVariable, PrologInterval> numbers =
            new LinkedHashMap<PrologAbstractVariable, PrologInterval>(this.getIntegerMap());
        ground.addAll(information.getGroundSet());
        free.addAll(information.getFreeSet());
        nonunify.addAll(information.getNonUnifyingTerms());
        for (Map.Entry<PrologAbstractVariable, PrologInterval> entry : information.getIntegerMap().entrySet()) {
            final PrologAbstractVariable key = entry.getKey();
            if (numbers.containsKey(key)) {
                numbers.put(key, numbers.get(key).intersect(entry.getValue()));
            } else {
                numbers.put(key, entry.getValue());
            }
        }
        // TODO: Unite expression vars and arithmetic state
        return
            KnowledgeBase.createCleanedKnowledgeBase(
                ground,
                free,
                nonunify,
                this.expressionVars,
                numbers,
                this.arithmeticState
            );
    }

    /**
     * During the abstract evaluation of a program it happens that a given abstract state is evaluated with a clause.
     * For more details on this, see "Giesl et al: Symbolic Evaluation Graphs and Term Rewriting". During this
     * evaluation, a new KnowledgeBase has to be created for the evaluated state. This happens in this method.
     * @param clause The program clause used in the evaluation (not the head of the evaluated state), with no
     *               substitution applied.
     * @param sigma The substitution used in the evaluation of the abstract state.
     * @param aborter For abortions.
     * @return The KnowledgeBase to be used in the evaluated state. Null if sigma is not compatible with this
     *         KnowledgeBase.
     */
    KnowledgeBase recordEvaluation(PrologClause clause, PrologSubstitution sigma, Abortion aborter) {
        final PrologTerm head = clause.getHead();
        PrologTerm body = clause.getBody();
        final PrologSubstitution sigmaG = sigma.restrict(this.getGroundSet());
        // G' = G \cup A(Range(sigma|_G))
        final Set<PrologAbstractVariable> ground = new LinkedHashSet<PrologAbstractVariable>(this.getGroundSet());
        ground.addAll(sigmaG.getAbstractVarsInRange());
        // exclusion = N(head)
        final Set<PrologNonAbstractVariable> exclusion = head.createSetOfAllNonAbstractVariables();
        // bVars = N(body)
        final Set<PrologNonAbstractVariable> bVars =
            (body == null ? new LinkedHashSet<PrologNonAbstractVariable>() : body.createSetOfAllNonAbstractVariables());
        // fRange = N(Range(sigma|_F))
        final Set<PrologNonAbstractVariable> fRange = sigma.restrict(this.getFreeSet()).getNonAbstractVarsInRange();
        // bVars = N(body) \ N(head)
        bVars.removeAll(exclusion);
        // exclusion = F \cup N(head)
        exclusion.addAll(this.getFreeSet());
        // fRange = N(Range(sigma|_F)) \ N(Range(sigma|_{N \ (F \cup N(head)})))
        fRange.removeAll(
            sigma.restrictToNonAbstractVariables().restrictExclusion(exclusion).getNonAbstractVarsInRange()
        );
        // F' = F \cup fRange \cup bVars
        final Set<PrologNonAbstractVariable> free = new LinkedHashSet<PrologNonAbstractVariable>(this.getFreeSet());
        free.addAll(fRange);
        free.addAll(bVars);
        // nonunify = U\sigma|_G
        final Set<Pair<PrologTerm, PrologTerm>> nonunify = new LinkedHashSet<Pair<PrologTerm, PrologTerm>>();
        for (Pair<PrologTerm, PrologTerm> pair : this.getNonUnifyingTerms()) {
            nonunify.add(new Pair<PrologTerm, PrologTerm>(pair.x.applySubstitution(sigmaG), pair.y
                .applySubstitution(sigmaG)));
        }
        // numbers is the map of the new integers TODO more precise documentation
        final PrologSubstitution sigmaI = sigma.restrict(this.getIntegerSet());
        final Map<PrologAbstractVariable, PrologInterval> numbers =
            new LinkedHashMap<PrologAbstractVariable, PrologInterval>(this.getIntegerMap());
        for (Map.Entry<PrologVariable, PrologTerm> entry : sigmaI.entrySet()) {
            final PrologVariable key = entry.getKey();
            final PrologTerm value = entry.getValue();
            if (value.isInt()) {
                if (!this.getIntegerMap().get(key).contains((PrologInt) value)) {
                    return null;
                }
            } else if (value.isAbstractVariable()) {
                numbers.put((PrologAbstractVariable) value, this.getIntegerMap().get(key));
            } else {
                return null;
            }
        }
        // E' = E \cup A(Range(sigma|_E))
        final Set<PrologAbstractVariable> expressionVars = new HashSet<>(this.expressionVars);
        expressionVars.addAll(sigma.restrict(this.expressionVars).getAbstractVarsInRange());
        // A = A \cup A\sigma
        final Map<IntegerVariable, FunctionalIntegerExpression> llvmSubstitution =
            this.termToRelationConverter.convertSubstitution(sigma);
        final Collection<IntegerRelation> renamedRelations = new LinkedList<>();
        for(IntegerRelation oldRelation : this.arithmeticState.toRelationSet()) {
            renamedRelations.add(oldRelation.applySubstitution(llvmSubstitution));
        }
        final IntegerState newArithmeticState = this.arithmeticState.addRelationSet(renamedRelations, aborter);
        return
            new KnowledgeBase(
                ground,
                free,
                nonunify,
                expressionVars,
                numbers,
                this.safeEvaluationHeuristic,
                this.termToRelationConverter,
                newArithmeticState
            );
    }

}
