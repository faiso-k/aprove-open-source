/*
 * Created on 11.04.2005
 */
package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.Unification.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A Term is a IVariable<?> or a IFunctionApplication<?> and nothing else! There are
 * no sorts, types, ConstructorApplications, ...
 * @author Martin Pluecker, copied from thiemann
 * @see IFunctionApplication<?>, IVariable<?>
 */
public abstract class ITerm<R extends SemiRing<R>> extends IDPExportable.IDPExportableSkeleton implements Immutable, IDPExportable,
XmlExportable, Comparable<ITerm<?>>, Iterable<ITerm<?>>, EdgeOrTerm, NodeOrTerm, BooleanPolyVarKeyable, HasVariables<IVariable<?>> {

    public final static String STANDARD_PREFIX = "x";
    public final static String SECOND_STANDARD_PREFIX = "y"; // all these prefixes have to be different!
    public final static String THIRD_STANDARD_PREFIX = "z";
    public final static int STANDARD_NUMBER = 0;

    /**
     * An empty array list provided for convenience and optimization for all
     * those IFunctionApplication<?>s of arity 0.
     */
    public final static ImmutableArrayList<ITerm<?>> EMPTY_ARGS =
        ImmutableCreator.create(new ArrayList<ITerm<?>>(0));

    /**
     * An empty set provided for convenience and optimization.
     */
    public final static ImmutableSet<ITerm<?>> EMPTY_SET =
        ImmutableCreator.create(Collections.<ITerm<?>> emptySet());

    /**
     * An empty set provided for convenience and optimization.
     */
    public final static ImmutableSet<IVariable<?>> EMPTY_VARIABLES =
        ImmutableCreator.create(Collections.<IVariable<?>> emptySet());

    /**
     * An empty set provided for convenience and optimization.
     */
    public static final ImmutableSet<ITerm<?>> EMPTY_TERMS =
        ImmutableCreator.create(Collections.<ITerm<?>> emptySet());;

    /**
     * creates a new IVariable<?>
     * @param name - a non null string
     * @return
     */
    public static <R extends SemiRing<R>> IVariable<R> createVariable(final String name,
        final SemiRingDomain<R> domain) {
        return new IVariable<R>(name, domain);
    }

    /**
     * creates a new Function Application from the arguments.
     * @param f - a symbol with arity n
     * @param args - a vector of arity n where all arguments are non-null
     */
    public static <D extends SemiRing<D>> IFunctionApplication<D> createFunctionApplication(final IFunctionSymbol<D> f,
        final ImmutableArrayList<? extends ITerm<?>> args) {
        return new IFunctionApplication<D>(f, args);
    }

    /**
     * creates a new Function Application from the arguments.
     * @param f - a symbol with arity n
     * @param args - a vector of arity n where all arguments are non-null
     */
    public static IFunctionApplication<?> createFunctionApplication(final IFunctionSymbol<?> f,
        final ArrayList<? extends ITerm<?>> args) {
        final ImmutableArrayList<? extends ITerm<?>> argsImmutable =
            ImmutableCreator.create(args);
        return ITerm.createFunctionApplication(f, argsImmutable);
    }

    /**
     * creates a new Function Application from the arguments.
     * @param f - a symbol with arity n
     * @param args - an array of arity n where all arguments are non-null
     */
    public static <D extends SemiRing<D>> IFunctionApplication<D> createFunctionApplication(final IFunctionSymbol<D> f,
        final ITerm<?>... args) {
        final ArrayList<ITerm<?>> v = new ArrayList<ITerm<?>>(args.length);
        for (final ITerm<?> t : args) {
            v.add(t);
        }
        return new IFunctionApplication<D>(f, ImmutableCreator.create(v));
    }

    /**
     * returns the set of Variables occuring in this term. The returned set may
     * The returned set may be modified
     */
    @Override
    public final Set<IVariable<?>> getVariables() {
        final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>();
        this.collectVariables(vars);
        return vars;
    }

    /**
     * adds all the Variables occurring in this term to the set vars
     * @param vars
     */
    public abstract void collectVariables(Set<IVariable<?>> vars);

    /**
     * @return a map which stores for the occurring Variables at which positions
     * they occur
     */
    public final Map<IVariable<?>, List<IPosition>> getVariablePositions() {
        final Map<IVariable<?>, List<IPosition>> vps =
            new LinkedHashMap<IVariable<?>, List<IPosition>>();
        this.collectVariablePositions(IPosition.create(), vps);
        return vps;
    }

    /**
     * For each occurring IVariable<?>, store in varPositions at which positions it
     * occurs.
     * @param pos - the position of this
     * @param varPositions - stores for each occurring IVariable<?> at which
     * positions it occurs in this; non-null
     */
    protected abstract void collectVariablePositions(IPosition pos,
        Map<IVariable<?>, List<IPosition>> varPositions);

    /**
     * returns the set of function symbols occuring in this term. This set may
     * be modified
     */
    public final Set<IFunctionSymbol<?>> getFunctionSymbols() {
        final Set<IFunctionSymbol<?>> fs = new LinkedHashSet<IFunctionSymbol<?>>();
        this.collectFunctionSymbols(fs);
        return fs;
    }

    /**
     * adds all the function symbols occurring in this term to the set fs
     * @param fs
     */
    public abstract void collectFunctionSymbols(Set<IFunctionSymbol<?>> fs);

    /**
     * returns a map from function symbols of this to their number of
     * occurrences
     * @return
     */
    public final Map<IFunctionSymbol<?>, Integer> getFunctionSymbolCount() {
        final Map<IFunctionSymbol<?>, Integer> result =
            new LinkedHashMap<IFunctionSymbol<?>, Integer>();
        this.computeFunctionSymbolCount(result);
        return result;
    }

    /**
     * adds all Variables occurring in this term to the map where occurrences
     * counts.
     * @param map
     */
    public abstract void computeFunctionSymbolCount(Map<IFunctionSymbol<?>, Integer> map);

    /**
     * returns the set of all positions in the term
     * @return
     */
    public final IPosition getLongestPrefixInTerm(final IPosition pos) {
        if (Globals.useAssertions) {
            assert (pos != null);
        }
        if (pos.isEmptyPosition()) {
            return pos;
        }
        final int[] posArray = pos.toIntArray();
        ITerm<?> actTerm = this;
        int depth = 0;
        while (depth < posArray.length && !actTerm.isVariable()) {
            final IFunctionApplication<?> fa = (IFunctionApplication<?>) actTerm;
            if (posArray[depth] < fa.getRootSymbol().getArity()) {
                actTerm = fa.getArgument(posArray[depth]);
                depth++;
            } else {
                break;
            }
        }
        if (depth == 0) {
            return IPosition.create();
        } else if (depth == posArray.length) {
            return pos;
        } else {
            final int[] res = new int[depth];
            System.arraycopy(posArray, 0, res, 0, depth - 1);
            return IPosition.create(res);
        }
    }

    /**
     * returns the set of all positions in the term
     * @return
     */
    public final boolean isValidPosition(final IPosition pos) {
        if (Globals.useAssertions) {
            assert (pos != null);
        }
        if (pos.isEmptyPosition()) {
            return true;
        }

        ITerm<?> current = this;
        for (final Integer p : pos) {
            if (current.isVariable()) {
                return false;
            } else {
                final IFunctionApplication<?> fa = (IFunctionApplication<?>) current;
                if (p < fa.getArguments().size()) {
                    current = fa.getArgument(p);
                } else {
                    return false;
                }
            }
        }

        return true;
    }

    /**
     * returns the set of all positions in the term
     * @return
     */
    public final Set<IPosition> getPositions() {
        final Set<IPosition> pts = new LinkedHashSet<IPosition>();
        final IPosition pos = IPosition.create();
        this.collectPositions(pos, pts);
        return pts;
    }

    /**
     * adds all positions of this term to the set pts. The position of the The
     * position of the current term is given with pos.
     * @param pos
     * @param pts
     */
    protected abstract void collectPositions(IPosition pos,
        Collection<IPosition> pts);

    /**
     * returns the set of all positions in the term with its corresponding
     * subterms
     * @return
     */
    public final Collection<Pair<IPosition, ITerm<?>>> getPositionsWithSubTerms() {
        final Collection<Pair<IPosition, ITerm<?>>> pts =
            new ArrayList<Pair<IPosition, ITerm<?>>>();

        final IPosition pos = IPosition.create();
        this.collectPositionsAndSubTerms(pos, pts, false, false);

        return pts;
    }

    /**
     * returns the set of all non-root and non-IVariable<?> positions with its
     * corresponding subterms
     */
    @SuppressWarnings("unchecked")
    public final Collection<Pair<IPosition, IFunctionApplication<?>>> getNonRootNonVariablePositionsWithSubTerms() {
        final Collection<Pair<IPosition, IFunctionApplication<?>>> pts =
            new ArrayList<Pair<IPosition, IFunctionApplication<?>>>();
        final IPosition pos = IPosition.create();
        this.collectPositionsAndSubTerms(pos, (Collection) pts, true, true);
        return pts;
    }

    /**
     * returns the set of all non-IVariable<?> positions with its
     * corresponding subterms sorted by root function symbols
     */
    public final Map<IFunctionSymbol<?>, Collection<Pair<IPosition, ITerm<?>>>> getSortedPositionsWithSubTerms() {
        final CollectionMap<IFunctionSymbol<?>, Pair<IPosition, ITerm<?>>> res = new CollectionMap<IFunctionSymbol<?>, Pair<IPosition, ITerm<?>>>();
        final IPosition pos = IPosition.create();
        this.collectSortedPositionssWithSubTerms(pos, res);
        return res;
    }

    protected abstract void collectSortedPositionssWithSubTerms(final IPosition pos,
        final CollectionMap<IFunctionSymbol<?>, Pair<IPosition, ITerm<?>>> res);

    /**
     * collects deepest application of giving function symbol
     */
    public final <E extends SemiRing<E>> Map<IPosition, IFunctionApplication<E>> getDeepestFunctionApplication(final Collection<IFunctionSymbol<E>> fs) {
        final Map<IPosition, IFunctionApplication<E>> res = new LinkedHashMap<IPosition, IFunctionApplication<E>>();
        final IPosition pos = IPosition.create();
        this.collectDeepestFunctionApplication(fs, pos, res);
        return res;
    }

    /**
     * @param fs
     * @return true iff nested function application of fs was found
     */
    protected abstract <E extends SemiRing<E>> boolean collectDeepestFunctionApplication(Collection<IFunctionSymbol<E>> fs, final IPosition pos,
        Map<IPosition, IFunctionApplication<E>> res);

    /**
     * adds all positions and subterms of this term to the set pts. The position
     * The position of the current term is given with pos.
     * @param pos
     * @param pts
     * @param dropRoot - if true, then the root position will not be counted
     * @param dropVars - if true, then the IVariable<?> positions will not be
     * counted
     */
    protected abstract void collectPositionsAndSubTerms(IPosition pos,
        Collection<Pair<IPosition, ITerm<?>>> pts,
        boolean dropRoot,
        boolean dropVars);

    /**
     * applies the substitution sigma to the term
     * @param sigma - non null
     * @return this term if sigma has no effect or a new term where sigma has
     * been applied
     */
    public ITerm<R> applySubstitution(final BasicTermSubstitution sigma) {
        if (sigma.isEmpty()) {
            return this;
        }
        return this.processSubstitution(sigma);
    }

    protected abstract ITerm<R> processSubstitution(BasicTermSubstitution sigma);

    /**
     * checks whether this and that are unifiable
     * @param that
     * @return
     */
    public final boolean unifies(final ITerm<?> that) {
        final Unification u = new Unification(this, that);
        return u.unify();
    }

    /**
     * checks whether this and that are unifiable with disjoint sets of
     * Variables
     * @param that
     * @return
     */
    public final boolean unifiesVarDisjoint(final ITerm<?> that) {
        final ITerm<?> thisRenamed =
            this.renumberVariables(ITerm.SECOND_STANDARD_PREFIX);
        final ITerm<?> thatRenamed =
            that.renumberVariables(ITerm.THIRD_STANDARD_PREFIX);
        return thisRenamed.unifies(thatRenamed);
    }

    /**
     * returns null, if terms are not unifiable. returns the mgu of this and
     * returns the mgu of this and that, otherwise.
     * @param other
     * @return
     */
    public final ISubstitution getMGU(final ITerm<?> that) {
        final Unification u = new Unification(this, that);

        return u.getMgu();
    }

    /**
     * delivers the new term this[t]_pos. I.e., we replace the subterm of this
     * of this at position pos by t. position of this.
     * @param pos - a valid position of this
     * @param t
     * @return
     */
    @SuppressWarnings("unchecked")
    public final ITerm<?> replaceAt(final IPosition pos, final ITerm<?> t) {
        final int[] positions = pos.toIntArray();
        final int depth = positions.length;
        final IFunctionSymbol<?>[] fs = new IFunctionSymbol<?>[depth];
        final ArrayList<? extends ITerm<?>>[] allArgs = (new ArrayList[depth]);
        ITerm<?> current = this;
        int i;
        for (i = 0; i < depth; i++) {
            final IFunctionApplication<?> fTerm = (IFunctionApplication<?>) current;
            fs[i] = fTerm.getRootSymbol();

            final List<? extends ITerm<?>> args = fTerm.getArguments();
            allArgs[i] = (ArrayList<? extends ITerm<?>>) args;
            current = args.get(positions[i]);
        }
        current = t;
        while (i != 0) {
            i--;
            final ArrayList<ITerm<?>> args = new ArrayList<ITerm<?>>(allArgs[i]);
            args.set(positions[i], current);
            current = IFunctionApplication.create(fs[i], ImmutableCreator.create(args));
        }
        return current;
    }

    /**
     * delivers a new term where all occurrences of the term replace are
     * replaced by the term replacement.
     * @param replace
     * @param replacement
     * @return
     */
    public final ITerm<?> replaceAll(final ITerm<?> replace, final ITerm<?> replacement) {
        if (Globals.useAssertions) {
            assert (replace != null && replacement != null);
        }
        if (this.equals(replace)) {
            return replacement;
        }
        if (this.isVariable()) {
            return this;
        }
        final IFunctionApplication<?> fThis = (IFunctionApplication<?>) this;
        boolean changed = false;
        final ImmutableArrayList<? extends ITerm<?>> args = fThis.getArguments();
        final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(args.size());
        for (final ITerm<?> arg : args) {
            final ITerm<?> newArg = arg.replaceAll(replace, replacement);
            if (newArg != arg) {
                changed = true;
            }
            newArgs.add(newArg);
        }

        if (changed) {
            return IFunctionApplication.create(fThis.getRootSymbol(),
                ImmutableCreator.create(newArgs));
        } else {
            return this;
        }
    }

    /**
     * delivers a new term where all occurrences of the term replace are
     * replaced by the term replacement.
     * @param replace
     * @param replacement
     * @return
     */
    public final ITerm<?> replaceAll(final Map<ITerm<?>, ITerm<?>> replaceMap) {
        if (Globals.useAssertions) {
            for (final ITerm<?> term : replaceMap.values()) {
                assert (term != null);
            }
        }
        return this.uncheckedReplaceAll(replaceMap);
    }

    private final ITerm<?> uncheckedReplaceAll(final Map<ITerm<?>, ITerm<?>> replaceMap) {
        final ITerm<?> replacement = replaceMap.get(this);
        if (replacement != null) {
            return replacement;
        }
        if (this.isVariable()) {
            return this;
        }
        final IFunctionApplication<?> fThis = (IFunctionApplication<?>) this;
        boolean changed = false;
        final ImmutableArrayList<? extends ITerm<?>> args = fThis.getArguments();
        final ArrayList<ITerm<?>> newArgs = new ArrayList<ITerm<?>>(args.size());
        for (final ITerm<?> arg : args) {
            final ITerm<?> newArg = arg.replaceAll(replaceMap);
            if (newArg != arg) {
                changed = true;
            }
            newArgs.add(newArg);
        }

        if (changed) {
            return IFunctionApplication.create(fThis.getRootSymbol(),
                ImmutableCreator.create(newArgs));
        } else {
            return this;
        }
    }

    /**
     * delivers a new term where all occurrences of the function symbol replace
     * are replaced by the corresponding replacement. The new function symbol
     * must have the same arity as the new one.
     * @param replace
     * @param replacement
     * @return
     */
    public abstract ITerm<?> replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap);

    protected abstract ITerm<?> uncheckedreplaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap);

    /**
     * checks whether this term has sub as a subterm, i.e. whether there is some
     * position p such that this|_p = sub. This method is equivalent to This
     * method is equivalent to this.getSubterms.contains(sub), but it
     * @param sub
     * @return
     */
    public final boolean hasSubterm(final ITerm<?> sub) {
        if (Globals.useAssertions) {
            assert (sub != null);
        }
        if (this.equals(sub)) {
            return true;
        }
        if (this.isVariable()) {
            return false;
        }

        for (final ITerm<?> arg : ((IFunctionApplication<R>) this).getArguments()) {
            if (arg.hasSubterm(sub)) {
                return true;
            }
        }

        return false;
    }

    /**
     * checks whether this term has sub as a subterm, i.e. whether there is some
     * position p such that this|_p = sub. This method is equivalent to This
     * method is equivalent to this.getSubterms.contains(sub), but it
     * @param sub
     * @return
     */
    public final Set<IPosition> getSubtermPositions(final ITerm<?> sub) {
        return this.getSubtermPositions(sub, IPosition.EMPTY);
    }

    public final Set<IPosition> getSubtermPositions(final ITerm<?> sub, final IPosition currentPos) {
        if (Globals.useAssertions) {
            assert (sub != null);
        }
        if (this.equals(sub)) {
            return Collections.singleton(currentPos);
        }
        if (this.isVariable()) {
            return Collections.emptySet();
        }

        final Set<IPosition> result = new LinkedHashSet<IPosition>();
        final IFunctionApplication<R> fa = (IFunctionApplication<R>) this;
        final ImmutableArrayList<ITerm<?>> arguments = fa.getArguments();
        final int size = arguments.size();

        for (int i = 0; i < size; i++) {
            result.addAll(
                arguments.get(i).getSubtermPositions(
                    sub,
                    currentPos.append(i)));
        }

        return result;
    }

    /**
     * checks whether this term has sub as proper subterm, i.e. whether there is
     * some non-empty position p such that this|_p = sub.
     */
    public final boolean hasProperSubterm(final ITerm<?> sub) {
        if (Globals.useAssertions) {
            assert (sub != null);
        }
        if (this.isVariable()) {
            return false;
        }

        for (final ITerm<?> arg : ((IFunctionApplication<R>) this).getArguments()) {
            if (arg.hasSubterm(sub)) {
                return true;
            }
        }

        return false;
    }

    /**
     * This method eturns the subterm of this term at position <code>pos</code>.
     * The caller has to ensure that <code>pos</code> is a valid position of
     * this term.
     * @param pos
     * @return
     */
    public final ITerm<?> getSubterm(final IPosition pos) {
        if (Globals.useAssertions) {
            assert (pos != null);
        }
        if (pos.isEmptyPosition()) {
            return this;
        }
        final int[] posArray = pos.toIntArray();
        ITerm<?> actTerm = this;
        IFunctionApplication<?> actFunc = (IFunctionApplication<?>) this;
        final int toDepth = posArray.length;
        for (int i = 0; i < toDepth - 1; i++) {
            actTerm = actFunc.getArgument(posArray[i]);
            actFunc = (IFunctionApplication<?>) actTerm;
        }
        if (toDepth > 0) {
            actTerm = actFunc.getArgument(posArray[toDepth - 1]);
        }
        return actTerm;
    }

    /**
     * This method eturns the subterm of this term at position <code>pos</code>.
     * The caller has not to ensure that <code>pos</code> is a valid position of
     * this term. it returns null for invalid positions
     * @param pos
     * @return
     */
    public final ITerm<?> getSubtermOrNull(final IPosition pos) {
        if (Globals.useAssertions) {
            assert (pos != null);
        }
        if (pos.isEmptyPosition()) {
            return this;
        }
        final int[] posArray = pos.toIntArray();
        ITerm<?> actTerm = this;
        IFunctionApplication<?> actFunc;
        for (int i = 0; i < pos.getDepth(); i++) {
            if (actTerm.isVariable()) {
                return null;
            }
            actFunc = (IFunctionApplication<?>) actTerm;
            final int p = posArray[i];
            if (p >= actFunc.getRootSymbol().getArity()) {
                return null;
            }
            actTerm = actFunc.getArgument(p);
        }
        return actTerm;
    }

    /**
     * delivers a new term where every IVariable<?> is renamed to prefix_nr. The
     * numbers start with STANDARD_NUMBER and are incr. each time a new
     * IVariable<?> is spotted. The term is traversed from left to right. E.g., if
     * this = f(x,y,g(x1,x),y,z) prefix = x STANDARD_NUMBER = 0 then the result
     * will be f(x0,x1,g(x2,x0),x1,x3) then the result will be
     * f(x0,x1,g(x2,x0),x1,x3)
     * @param prefix
     * @return
     */
    public final ITerm<?> renumberVariables(final String prefix) {
        return this.renumberVariables(
            new LinkedHashMap<IVariable<?>, IVariable<?>>(), prefix, ITerm.STANDARD_NUMBER).x;
    }

    /**
     * Returns true if the name of every IVariable<?> in this term starts with the
     * string prefix.
     * @param prefix
     * @return
     */
    public boolean checkVariablePrefix(final String prefix) {
        for (final IVariable<?> v : this.getVariables()) {
            if (!v.getName().startsWith(prefix)) {
                return false;
            }
        }
        return true;
    }

    /**
     * returns the term where we renumber the Variables with the
     * STANDARD_PREFIX.
     * @see renumberVariables
     * @return
     */
    public final ITerm<?> getStandardRenumbered() {
        return this.renumberVariables(new HashMap<IVariable<?>, IVariable<?>>(),
            ITerm.STANDARD_PREFIX, ITerm.STANDARD_NUMBER).x;
    }

    /**
     * Gets a renumbering map, a prefix, and the next free nr. First, for all
     * Variables x in the term that do not occur in the keyset of the map we add
     * the assignment x/prefix_freeNr to the map and update the free nr counter
     * accordingly. Then we replace all Variables in the term by their
     * corresponding Variables in the map. The result is the pair of the new
     * term and the next free nr.
     * @param map
     * @param prefix
     * @param nr
     * @return
     */
    public abstract ImmutablePair<? extends ITerm<?>, Integer> renumberVariables(Map<IVariable<?>, IVariable<?>> map,
        String prefix,
        Integer nr);

    /**
     * all Variables in the term will be renamed to new ones, where different
     * occurences of the same Variables will be renamed to the same new
     * IVariable. It is guaranteed, that no IVariable<?> of vars will be present in
     * the term afterwards.
     * @param vars
     * @return
     */
    public final ITerm<?> renameVariables(final Collection<IVariable<?>> vars) {
        return this.renameVariables(new aprove.verification.idpframework.Core.Utility.FreshVarGenerator(
            vars));
    }

    /**
     * returns a map from Variables of this to their nr of occurence
     * @return
     */
    public final Map<IVariable<?>, Integer> getVariableCount() {
        final Map<IVariable<?>, Integer> result =
            new LinkedHashMap<IVariable<?>, Integer>();
        this.computeVariableCount(result);
        return result;
    }

    /**
     * checks whether for each IVariable<?> of this term the nr of occurrences in
     * this term is not larger than the number given in the map. Requires that
     * the map contains values >= 0 for all Variables of this term. This method
     * @return
     */
    public final boolean hasLessVariablesThan(final Map<IVariable<?>, Integer> map) {
        return this.testForLessVariables(map);
    }

    /**
     * removes the nr of occurrences of this Variables from the map, if all
     * resulting values are >= 0. Then true is returned, otherwise false. It is
     * assumed that the map contains values >= 0 for all Variables occurring in
     * this term
     */
    protected abstract boolean testForLessVariables(Map<IVariable<?>, Integer> map);

    /**
     * adds all Variables occurring in this term to the map where occurrences
     * counts.
     * @param map
     */
    public abstract void computeVariableCount(Map<IVariable<?>, Integer> map);

    /**
     * all Variables in the term will be renamed to new ones, where different
     * occurences of the same Variables will be renamed to the same new the same
     * new IVariable. The generator gen is used to produce
     * @param gen
     * @return
     */
    public abstract ITerm<?> renameVariables(final aprove.verification.idpframework.Core.Utility.FreshVarGenerator gen);

    protected abstract ITerm<?> renameVariables(final aprove.verification.idpframework.Core.Utility.FreshVarGenerator gen,
        Map<IVariable<?>, IVariable<?>> map);

    /**
     * checks whether this matches that, that this sigma = that
     * @param that
     * @return
     */
    public final boolean matches(final ITerm<?> that) {
        Map<IVariable<?>, ITerm<?>> sigma = new LinkedHashMap<IVariable<?>, ITerm<?>>();
        sigma = this.extendMatchingSubstitution(sigma, that, false);
        return sigma != null;
    }

    /**
     * checks that if we first rename every IVariable<?> in this to a fresh
     * IVariable<?> if then this newly term matches that. If this is linear this is
     * term matches that. If this is linear this is matches and
     * this.linearMatches(that) = false implies this.matches(that) = This method
     * is more efficient than matches and this.linearMatches(that) =
     * this.matches(that) for linear terms this
     */
    public abstract boolean linearMatches(ITerm<?> that);

    public final ISubstitution getMatcher(final ITerm<?> that) {
        return this.getMatcher(that, false);
    }

    /**
     * returns the matcher of this and that if it exists, and null otherwise. *
     * @param that
     * @return
     * @see matches
     */
    public final ISubstitution getMatcher(final ITerm<?> that, final boolean weakUnknownDomain) {
        Map<IVariable<?>, ITerm<?>> sigma = new LinkedHashMap<IVariable<?>, ITerm<?>>();

        sigma = this.extendMatchingSubstitution(sigma, that, weakUnknownDomain);

        if (sigma == null) {
            return null;
        } else {
            return ISubstitution.create(ImmutableCreator.create(sigma));
        }
    }

    /**
     * extends the substitution sigma to some sigma' such that that. Here
     * extension means that sigma(x) = sigma'(x) for all x in keyset(sigma). If
     * such a sigma' exists we return sigma', otherwise null. sigma itself will
     * / may be modified!
     * @param sigma
     * @param that
     * @param weakUnknownDomain
     * @return
     */
    public abstract Map<IVariable<?>, ITerm<?>> extendMatchingSubstitution(Map<IVariable<?>, ITerm<?>> sigma,
        ITerm<?> that, boolean weakUnknownDomain);

    /**
     * checks whether a term is linear, i.e., whether it does not contain some
     * IVariable<?> twice.
     * @return
     */
    public final boolean isLinear() {
        return this.isLinear(new HashSet<IVariable<?>>());
    }

    /**
     * checks whether this term is linear, does not contain Variables of the
     * given set, and if this is true it adds its own Variables to the set
     * @param alreadyPresent
     * @return
     */
    protected abstract boolean isLinear(Set<IVariable<?>> alreadyPresent);

    /**
     * returns the set of subterms of this term. The set may be modified
     * @return
     */
    public final Set<ITerm<?>> getSubTerms() {
        final Set<ITerm<?>> subs = new LinkedHashSet<ITerm<?>>();
        this.collectSubTerms(subs, false);
        return subs;
    }

    /**
     * returns the set of non-IVariable<?> subterms of this term. the set may be
     * modified.
     */
    @SuppressWarnings("unchecked")
    public final Set<IFunctionApplication<?>> getNonVariableSubTerms() {
        final Set<ITerm<?>> subs = new LinkedHashSet<ITerm<?>>();
        this.collectSubTerms(subs, true);
        final Set<IFunctionApplication<?>> res = (Set) subs;
        return res;
    }

    public abstract void collectSubTerms(Set<ITerm<?>> subs, boolean dropVars);

    public abstract boolean isVariable();

    /**
     * return the maximal depth of a term where a constant has depth 0!
     */
    public abstract int getDepth();

    /**
     * return the maximal depth of a term where a constant has depth 1!
     */
    public abstract int getDepthConstant();

    /**
     * return the absolute number of Variables and function symbols in a term.
     */
    public abstract int getSize();

    /**
     * @returns The out domain of this term.
     */
    public abstract SemiRingDomain<R> getDomain();

    /**
     * @return The ring of the domain.
     */
    public R getRing() {
        return this.getDomain().getRing();
    }

    /**
     * rewrites the ITerm<?> as often as possible using the provided rule. One
     * better makes sure the rule to apply is terminating.
     */
    public ITerm<?> rewriteAsOftenAsPossible(final UnconditionalIRule r) {
        final ITerm<?> tmpResult = this;
        for (final Pair<IPosition, ITerm<?>> actPair : tmpResult.getPositionsWithSubTerms()) {
            final ITerm<?> subterm = actPair.y;
            if (subterm.isVariable()) {
                continue;
            }
            final IFunctionApplication<?> lhs = r.getLeft();
            final ISubstitution matcher = lhs.getMatcher(subterm);
            if (matcher != null) {
                return this.replaceAt(actPair.x,
                    r.getRight().applySubstitution(matcher)).rewriteAsOftenAsPossible(
                        r);
            }
        }
        return tmpResult; // No more applications possible.
    }

    /**
     * returns all terms which result out of all possible rewritings in R. The
     * returned set may safely be modified.
     */
    public Set<ITerm<?>> rewrite(final Map<IFunctionSymbol<?>, ? extends Set<? extends UnconditionalIRule>> R,
        final FreshNameGenerator freshNames) {
        final Set<ITerm<?>> rewritings = new LinkedHashSet<ITerm<?>>();
        Set<? extends UnconditionalIRule> usefulRules;
        for (final Pair<IPosition, ITerm<?>> actPair : this.getPositionsWithSubTerms()) {
            final ITerm<?> subterm = actPair.y;
            if (subterm.isVariable()) {
                continue;
            }
            final IFunctionApplication<?> fSubterm =
                (IFunctionApplication<?>) subterm;
            if ((usefulRules = R.get(fSubterm.getRootSymbol())) == null) {
                continue;
            }
            for (final UnconditionalIRule actRule : usefulRules) {
                final IFunctionApplication<?> lhs = actRule.getLeft();
                ISubstitution matcher = lhs.getMatcher(subterm);
                if (matcher != null) {
                    final Map<IVariable<?>, ITerm<?>> freshVars =
                        new LinkedHashMap<IVariable<?>, ITerm<?>>(matcher.getMap());

                    final int i = 0;

                    for (final IVariable<?> var : actRule.getRight().getVariables()) {
                        if (!freshVars.containsKey(var)) {
                            freshVars.put(var, ITerm.createVariable(
                                freshNames.getFreshName("x" + i, false),
                                var.getDomain()));
                        }
                    }

                    matcher =
                        ISubstitution.create(ImmutableCreator.create(freshVars),
                            true);

                    rewritings.add(this.replaceAt(actPair.x,
                        actRule.getRight().applySubstitution(matcher)));
                }
            }
        }
        return rewritings;
    }

    public abstract boolean isConstant();

    /**
     * self-speaking method;
     * @author Martin Pluecker, copied from Sebastian Weise
     */
    public abstract boolean isGroundTerm();

    /**
     * this method returns a new ITerm<?> in which all occurences of the IVariable<?>
     * "IVariable<?>" are replaced by fresh pairwise disjunct Variables
     * @author Martin Pluecker, copied from Sebastian Weise
     */
    public ITerm<R> linearize(final IVariable<?> variable) {
        return this.helpLinearize(variable, this.getVariables());
    }

    protected abstract ITerm<R> helpLinearize(IVariable<?> variable,
        Set<IVariable<?>> toAvoid);

    @Override
    public Iterator<ITerm<?>> iterator() {
        return new TermIterator(this);
    }

    private static class TermIterator implements Iterator<ITerm<?>> {

        private final Stack<ITerm<?>> stack;

        public TermIterator(final ITerm<?> t) {
            this.stack = new Stack<ITerm<?>>();
            this.stack.push(t);
        }

        @Override
        public boolean hasNext() {
            return !this.stack.isEmpty();
        }

        @Override
        public ITerm<?> next() {
            final ITerm<?> t = this.stack.pop();
            if (!t.isVariable()) {
                final IFunctionApplication<?> funapp = (IFunctionApplication<?>) t;

                for (final ITerm<?> arg : funapp.getArguments()) {
                    this.stack.push(arg);
                }
            }
            return t;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
}
