package aprove.input.Programs.prolog.structure;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author cryingshadow
 *
 */
public abstract class PrologTerms {

    /**
     * Flag whether the replacement of non-abstract variables should be preferred by default.
     */
    public static final boolean PREFER_NONABSTRACT_REPLACEMENTS = true;

    /**
     * Flag whether the occurs-check should be applied by default.
     */
    public static final boolean USE_OCCURS_CHECK = true;

    /**
     * No object.
     */
    private PrologTerms() {
    }

    /**
     * Adds all terms from toAdd to set modulo variants.
     * @param set The set where to add terms to.
     * @param toAdd The terms to add.
     * @return True if set has been modified.
     */
    public static
        boolean
        addAllModuloNonAbstractVariableRenaming(final Set<PrologTerm> set, final Set<PrologTerm> toAdd)
    {
        final Set<PrologTerm> addSet = new LinkedHashSet<PrologTerm>();
        for (final PrologTerm addTerm : toAdd) {
            boolean in = false;
            for (final PrologTerm setTerm : set) {
                if (setTerm.equalsWithNonAbstractVariableNameChanging(addTerm)) {
                    in = true;
                    break;
                }
            }
            if (!in) {
                addSet.add(addTerm);
            }
        }
        if (addSet.isEmpty()) {
            return false;
        } else {
            set.addAll(addSet);
            return true;
        }
    }

    /**
     * General unification algorithm.
     * @param term1 The first term to be unified.
     * @param term2 The second term to be unified.
     * @param occursCheck Flag whether or not to apply the occurs-check.
     * @param nonAbstractReplacementPreferred Flag whether or not to prefer the replacement of non-abstract variables.
     * @return The mgu of the specified terms or null if it does not exist.
     */
    public static PrologSubstitution calculateMGU(
        final PrologTerm term1,
        final PrologTerm term2,
        final boolean occursCheck,
        final boolean nonAbstractReplacementPreferred)
    {
        final PrologSubstitution res = new PrologSubstitution();
        if (term1.isVariable()) {
            if (term2.isVariable()) {
                if (term1.equals(term2)) {
                    return res;
                }
                if (term1.isAbstractVariable() && !term2.isAbstractVariable()) {
                    if (nonAbstractReplacementPreferred) {
                        res.put((PrologVariable) term2, term1);
                    } else {
                        res.put((PrologVariable) term1, term2);
                    }
                } else {
                    if (nonAbstractReplacementPreferred) {
                        res.put((PrologVariable) term1, term2);
                    } else {
                        res.put((PrologVariable) term2, term1);
                    }
                }
                return res;
            } else {
                if (occursCheck) {
                    if (!term2.occurs(term1)) {
                        res.put((PrologVariable) term1, term2);
                        return res;
                    }
                } else {
                    if (term2.occurs(term1)) {
                        res.put((PrologVariable) term1, term2.toCyclic((PrologVariable) term1));
                        return res;
                    } else {
                        res.put((PrologVariable) term1, term2);
                        return res;
                    }
                }
            }
        } else if (term2.isVariable()) {
            if (occursCheck) {
                if (!term1.occurs(term2)) {
                    res.put((PrologVariable) term2, term1);
                    return res;
                }
            } else {
                if (term1.occurs(term2)) {
                    res.put((PrologVariable) term2, term1.toCyclic((PrologVariable) term2));
                    return res;
                } else {
                    res.put((PrologVariable) term2, term1);
                    return res;
                }
            }
        } else if (term1.getName().equals(term2.getName()) && term1.getArity() == term2.getArity()) {
            // corresponds to equal function symbols, i.e.,
            // term1.createFunctionSymbol().equals(term2.createFunctionSymbol())
            PrologTerm t1 = term1;
            PrologTerm t2 = term2;
            for (int i = 0; i < t1.getArity(); i++) {
                final Map<PrologVariable, PrologTerm> mgu =
                    PrologTerms.calculateMGU(
                        t1.getArgument(i),
                        t2.getArgument(i),
                        occursCheck,
                        nonAbstractReplacementPreferred);
                if (mgu == null) {
                    return null;
                } else {
                    // replaces the terms immediately to avoid clashes in
                    // substitutions
                    final Pair<PrologTerm, PrologTerm> pair = PrologTerms.combineMGUforArguments(t1, t2, i, mgu, res);
                    t1 = pair.x;
                    t2 = pair.y;
                }
            }
            return res;
        }
        return null;
    }

    /**
     * @param terms
     * @return
     */
    public static PrologSubstitution calculateMGU(
        final Set<PrologTerm> terms,
        final boolean occursCheck,
        final boolean nonAbstractReplacementPreferred)
    {
        if (terms == null) {
            throw new NullPointerException();
        }
        if (terms.size() < 2) {
            return new PrologSubstitution();
        }
        final Iterator<PrologTerm> iterator = terms.iterator();
        PrologTerm t1 = iterator.next();
        PrologTerm t2 = iterator.next();
        PrologSubstitution mgu = PrologTerms.calculateMGU(t1, t2, occursCheck, nonAbstractReplacementPreferred);
        while (iterator.hasNext() && mgu != null) {
            if (t1.isVariable()) {
                if (mgu.containsKey(t1)) {
                    t1 = mgu.get(t1);
                }
            } else {
                t1 = t1.applySubstitution(mgu);
            }
            t2 = iterator.next();
            mgu = PrologTerms.calculateMGU(t1, t2, occursCheck, nonAbstractReplacementPreferred);
        }
        return mgu;
    }

    /**
     * @param term
     * @param h
     * @param kb
     * @return
     */
    public static PrologSubstitution calculateMGUwithOnlyFreshVariables(
        PrologTerm term1,
        PrologTerm term2,
        final boolean occursCheck,
        final boolean nonAbstractReplacementPreferred,
        final Set<PrologVariable> freshVars,
        final FreshNameGenerator fridge)
    {
        final PrologSubstitution res = new PrologSubstitution();
        if (term1.isVariable()) {
            if (term2.isVariable()) {
                if (term1.equals(term2)) {
                    return res;
                } else {
                    if (nonAbstractReplacementPreferred) {
                        if (freshVars.contains(term1) && (term1.isAbstractVariable() || term2.isNonAbstractVariable()))
                        {
                            res.put((PrologVariable) term2, term1);
                        } else if (freshVars.contains(term2)
                            && (term2.isAbstractVariable() || term1.isNonAbstractVariable()))
                        {
                            res.put((PrologVariable) term1, term2);
                        } else if (term1.isNonAbstractVariable() && term2.isNonAbstractVariable()) {
                            final PrologNonAbstractVariable fresh =
                                new PrologNonAbstractVariable(fridge.getFreshName("X", false));
                            res.put((PrologVariable) term1, fresh);
                            res.put((PrologVariable) term2, fresh);
                            freshVars.add(fresh);
                        } else {
                            final PrologAbstractVariable fresh =
                                new PrologAbstractVariable(fridge.getFreshName("T", false));
                            res.put((PrologVariable) term1, fresh);
                            res.put((PrologVariable) term2, fresh);
                            freshVars.add(fresh);
                        }
                        return res;
                    } else {
                        if (freshVars.contains(term1) && (term2.isAbstractVariable() || term1.isNonAbstractVariable()))
                        {
                            res.put((PrologVariable) term2, term1);
                        } else if (freshVars.contains(term2)
                            && (term1.isAbstractVariable() || term2.isNonAbstractVariable()))
                        {
                            res.put((PrologVariable) term1, term2);
                        } else {
                            final PrologNonAbstractVariable fresh =
                                new PrologNonAbstractVariable(fridge.getFreshName("X", false));
                            res.put((PrologVariable) term1, fresh);
                            res.put((PrologVariable) term2, fresh);
                            freshVars.add(fresh);
                        }
                        return res;
                    }
                }
            } else {
                for (final PrologVariable v : term2.createSetOfAllVariables()) {
                    if (freshVars.contains(v)) {
                        if (term1.isAbstractVariable() && v.isNonAbstractVariable()) {
                            final PrologVariable fresh = new PrologAbstractVariable(fridge.getFreshName("T", false));
                            res.put(v, fresh);
                            freshVars.add(fresh);
                        }
                    } else {
                        PrologVariable fresh;
                        if (term1.isAbstractVariable() || v.isAbstractVariable()) {
                            fresh = new PrologAbstractVariable(fridge.getFreshName("T", false));
                        } else {
                            fresh = new PrologNonAbstractVariable(fridge.getFreshName("X", false));
                        }
                        res.put(v, fresh);
                        freshVars.add(fresh);
                    }
                }
                if (occursCheck) {
                    if (term2.occurs(term1)) {
                        return null;
                    } else {
                        res.put((PrologVariable) term1, term2.applySubstitution(res));
                        return res;
                    }
                } else {
                    if (term2.occurs(term1)) {
                        final PrologTerm cycle = term2.toCyclic((PrologVariable) term1).applySubstitution(res);
                        res.put((PrologVariable) term1, cycle);
                        return res;
                    } else {
                        res.put((PrologVariable) term1, term2.applySubstitution(res));
                        return res;
                    }
                }
            }
        } else if (term2.isVariable()) {
            for (final PrologVariable v : term1.createSetOfAllVariables()) {
                if (freshVars.contains(v)) {
                    if (term2.isAbstractVariable() && v.isNonAbstractVariable()) {
                        final PrologVariable fresh = new PrologAbstractVariable(fridge.getFreshName("T", false));
                        res.put(v, fresh);
                        freshVars.add(fresh);
                    }
                } else {
                    PrologVariable fresh;
                    if (term2.isAbstractVariable() || v.isAbstractVariable()) {
                        fresh = new PrologAbstractVariable(fridge.getFreshName("T", false));
                    } else {
                        fresh = new PrologNonAbstractVariable(fridge.getFreshName("X", false));
                    }
                    res.put(v, fresh);
                    freshVars.add(fresh);
                }
            }
            if (occursCheck) {
                if (term1.occurs(term2)) {
                    return null;
                } else {
                    res.put((PrologVariable) term2, term1.applySubstitution(res));
                    return res;
                }
            } else {
                if (term1.occurs(term2)) {
                    final PrologTerm cycle = term1.toCyclic((PrologVariable) term2).applySubstitution(res);
                    res.put((PrologVariable) term2, cycle);
                    return res;
                } else {
                    res.put((PrologVariable) term2, term1.applySubstitution(res));
                    return res;
                }
            }
        } else if (term1.getName().equals(term2.getName()) && term1.getArity() == term2.getArity()) {
            // corresponds to equal function symbols, i.e.,
            // term1.createFunctionSymbol().equals(term2.createFunctionSymbol())
            for (int i = 0; i < term1.getArity(); i++) {
                final Map<PrologVariable, PrologTerm> mgu =
                    PrologTerms.calculateMGUwithOnlyFreshVariables(
                        term1.getArgument(i),
                        term2.getArgument(i),
                        occursCheck,
                        nonAbstractReplacementPreferred,
                        freshVars,
                        fridge);
                if (mgu == null) {
                    return null;
                } else {
                    // replaces the terms immediately to avoid clashes in
                    // substitutions
                    final Pair<PrologTerm, PrologTerm> pair =
                        PrologTerms.combineMGUforArguments(term1, term2, i, mgu, res);
                    term1 = pair.x;
                    term2 = pair.y;
                }
            }
            return res;
        }
        return null;
    }

    /**
     * @param terms
     * @return
     */
    public static PrologSubstitution calculateMGUwithOnlyFreshVariables(
        final Set<PrologTerm> terms,
        final boolean occursCheck,
        final boolean nonAbstractReplacementPreferred,
        final Set<PrologVariable> freshVars,
        final FreshNameGenerator fridge)
    {
        if (terms == null) {
            throw new NullPointerException();
        }
        if (terms.size() < 2) {
            return new PrologSubstitution();
        }
        final Iterator<PrologTerm> iterator = terms.iterator();
        PrologTerm t1 = iterator.next(), t2 = iterator.next();
        PrologSubstitution mgu =
            PrologTerms.calculateMGUwithOnlyFreshVariables(
                t1,
                t2,
                occursCheck,
                nonAbstractReplacementPreferred,
                freshVars,
                fridge);
        while (iterator.hasNext() && mgu != null) {
            if (t1.isVariable()) {
                if (mgu.containsKey(t1)) {
                    t1 = mgu.get(t1);
                }
            } else {
                t1 = t1.applySubstitution(mgu);
            }
            t2 = iterator.next();
            mgu =
                PrologTerms.calculateMGUwithOnlyFreshVariables(
                    t1,
                    t2,
                    occursCheck,
                    nonAbstractReplacementPreferred,
                    freshVars,
                    fridge);
        }
        return mgu;
    }

    public static PrologSubstitution calculateMGUwithoutAbstractVariableUnification(
        PrologTerm term1,
        PrologTerm term2,
        final boolean occursCheck)
    {
        final PrologSubstitution res = new PrologSubstitution();
        if (term1.isNonAbstractVariable() && term2.isNonAbstractVariable()) {
            if (term1.equals(term2)) {
                return res;
            } else {
                res.put((PrologVariable) term1, term2);
                return res;
            }
        } else if (term1.isNonAbstractVariable()) {
            if (occursCheck && !term2.occurs(term1)) {
                res.put((PrologVariable) term1, term2);
                return res;
            } else if (!occursCheck) {
                if (term2.occurs(term1)) {
                    res.put((PrologVariable) term1, term2.toCyclic((PrologVariable) term1));
                    return res;
                } else {
                    res.put((PrologVariable) term1, term2);
                    return res;
                }
            }
        } else if (term2.isNonAbstractVariable()) {
            if (occursCheck && !term1.occurs(term2)) {
                res.put((PrologVariable) term2, term1);
                return res;
            } else if (!occursCheck) {
                if (term1.occurs(term2)) {
                    res.put((PrologVariable) term2, term1.toCyclic((PrologVariable) term2));
                    return res;
                } else {
                    res.put((PrologVariable) term2, term1);
                    return res;
                }
            }
        } else if (term1.getName().equals(term2.getName()) && term1.getArity() == term2.getArity()) {
            for (int i = 0; i < term1.getArity(); i++) {
                final Map<PrologVariable, PrologTerm> mgu =
                    PrologTerms.calculateMGUwithoutAbstractVariableUnification(
                        term1.getArgument(i),
                        term2.getArgument(i),
                        occursCheck);
                if (mgu == null) {
                    return null;
                }
                for (final Map.Entry<PrologVariable, PrologTerm> entry : mgu.entrySet()) {
                    for (final Map.Entry<PrologVariable, PrologTerm> e : res.entrySet()) {
                        res.put(e.getKey(), e.getValue().replaceAll(entry.getKey(), entry.getValue()));
                    }
                    res.put(entry.getKey(), entry.getValue());
                    for (int j = i + 1; j < term1.getArity(); j++) {
                        term1 =
                            term1.replaceArgument(j, term1.getArgument(j).replaceAll(entry.getKey(), entry.getValue()));
                        term2 =
                            term2.replaceArgument(j, term2.getArgument(j).replaceAll(entry.getKey(), entry.getValue()));
                    }
                }
            }
            return res;
        }
        return null;
    }

    /**
     * @param terms
     * @return
     */
    public static PrologSubstitution calculateMGUwithoutAbstractVariableUnification(
        final Set<PrologTerm> terms,
        final boolean occursCheck)
    {
        if (terms == null) {
            throw new NullPointerException();
        }
        if (terms.size() < 2) {
            return new PrologSubstitution();
        }
        final Iterator<PrologTerm> iterator = terms.iterator();
        PrologTerm t1 = iterator.next(), t2 = iterator.next();
        PrologSubstitution mgu = PrologTerms.calculateMGUwithoutAbstractVariableUnification(t1, t2, occursCheck);
        while (iterator.hasNext() && mgu != null) {
            if (t1.isVariable()) {
                if (mgu.containsKey(t1)) {
                    t1 = mgu.get(t1);
                }
            } else {
                t1 = t1.applySubstitution(mgu);
            }
            t2 = iterator.next();
            mgu = PrologTerms.calculateMGUwithoutAbstractVariableUnification(t1, t2, occursCheck);
        }
        return mgu;
    }

    /**
     * Tests whether or not the specified collection contains a match
     * for the specified predicate.
     * @param predicate The predicate to look for.
     * @param collection The collection to look in.
     * @return True, if the specified predicate matches at least one term
     *         in the specified collection. False otherwise.
     */
    public static boolean containsMatch(final FunctionSymbol predicate, final Collection<PrologTerm> collection) {
        for (final PrologTerm t : collection) {
            if (t.hasEqualFunctionSymbol(predicate)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Tests whether or not the specified collection contains a match
     * for the specified term.
     * @param term The term to look for.
     * @param collection The collection to look in.
     * @return True, if the specified term matches at least one term in
     *         the specified collection. False otherwise.
     */
    public static boolean containsMatch(final PrologTerm term, final Collection<PrologTerm> collection) {
        for (final PrologTerm t : collection) {
            if (t.hasEqualFunctionSymbol(term)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @param t
     * @param terms2
     * @return
     */
    public static boolean containsModuloNonAbstractVariableRenaming(final PrologTerm term, final Set<PrologTerm> terms)
    {
        for (final PrologTerm t : terms) {
            if (t.equalsWithNonAbstractVariableNameChanging(term)) {
                return true;
            }
        }
        return false;
    }

    public static PrologTerm createCall(final PrologTerm term) {
        final List<PrologTerm> args = new ArrayList<PrologTerm>();
        args.add(term);
        return new PrologTerm(PrologBuiltin.CALL_NAME, args);
    }

    /**
     * Creates a conjunction of all the terms in the specified list.
     * @param list The list of terms that should be conjuncted.
     * @return A conjunction of all the terms in the specified list.
     * @throws NullPointerException If the list is null.
     * @throws IllegalArgumentException If the list is empty.
     */
    public static PrologTerm createConjunction(final List<PrologTerm> list)
        throws NullPointerException,
            IllegalArgumentException
    {
        if (list.isEmpty()) {
            throw new IllegalArgumentException("The list is empty!");
        } else if (list.size() == 1) {
            return list.get(0);
        } else {
            final List<PrologTerm> rest = new ArrayList<PrologTerm>();
            for (int i = 1; i < list.size(); i++) {
                rest.add(list.get(i));
            }
            return PrologTerms.createConjunction(list.get(0), PrologTerms.createConjunction(rest));
        }
    }

    /**
     * Creates a new PrologTerm with name PrologBuiltin.CONJUNCTION_NAME,
     * arity 2 and the specified terms as arguments.
     * @param first The first argument of the conjunction.
     * @param second The second argument of the conjunction.
     * @return A conjunction of the specified terms.
     */
    public static PrologTerm createConjunction(final PrologTerm first, final PrologTerm second) {
        final List<PrologTerm> args = new ArrayList<PrologTerm>();
        args.add(first);
        args.add(second);
        return new PrologTerm(PrologBuiltin.CONJUNCTION_NAME, args);
    }

    /**
     * Creates a new cut.
     * @return A new cut.
     */
    public static PrologTerm createCut() {
        return new PrologTerm(PrologBuiltin.CUT_NAME);
    }

    /**
     * Creates a disjunction of all the terms in the specified list.
     * @param list The list of terms that should be disjuncted.
     * @return A disjunction of all the terms in the specified list.
     * @throws NullPointerException If the list is null.
     * @throws IllegalArgumentException If the list has less than two
     *                                  arguments.
     */
    public static PrologTerm createDisjunction(final List<PrologTerm> list) {
        if (list.size() < 2) {
            throw new IllegalArgumentException("A disjunction consists of at least two terms!");
        } else if (list.size() == 2) {
            return PrologTerms.createDisjunction(list.get(0), list.get(1));
        } else {
            final List<PrologTerm> rest = new ArrayList<PrologTerm>();
            for (int i = 1; i < list.size(); i++) {
                rest.add(list.get(i));
            }
            return PrologTerms.createDisjunction(list.get(0), PrologTerms.createDisjunction(rest));
        }
    }

    /**
     * Creates a new PrologTerm with name PrologBuiltin.DISJUNCTION_NAME,
     * arity 2 and the specified terms as arguments.
     * @param first The first argument of the disjunction.
     * @param second The second argument of the disjunction.
     * @return A disjunction of the specified terms.
     */
    public static PrologTerm createDisjunction(final PrologTerm first, final PrologTerm second) {
        final List<PrologTerm> args = new ArrayList<PrologTerm>();
        args.add(first);
        args.add(second);
        return new PrologTerm(PrologBuiltin.DISJUNCTION_NAME, args);
    }

    public static PrologTerm createEmptyList() {
        return new PrologTerm(PrologBuiltin.EMPTY_LIST_CONSTRUCTOR_NAME);
    }

    /**
     * Creates a new fail term.
     * @return A new fail term.
     */
    public static PrologTerm createFail() {
        return new PrologTerm(PrologBuiltin.FAIL_NAME);
    }

    /**
     * Creates a new if term with the specified arguments.
     * @param ifTerm The if term in question.
     * @param thenTerm The term to evaluate, if the if term is true.
     * @return A new if term.
     */
    public static PrologTerm createIf(final PrologTerm ifTerm, final PrologTerm thenTerm) {
        final List<PrologTerm> args = new ArrayList<PrologTerm>();
        args.add(ifTerm);
        args.add(thenTerm);
        return new PrologTerm(PrologBuiltin.IF_NAME, args);
    }

    public static PrologTerm createList(final List<PrologTerm> list) {
        if (list.isEmpty()) {
            return PrologTerms.createEmptyList();
        } else {
            final List<PrologTerm> rest = new ArrayList<PrologTerm>();
            for (int i = 1; i < list.size(); i++) {
                rest.add(list.get(i));
            }
            return PrologTerms.createList(list.get(0), PrologTerms.createList(rest));
        }
    }

    /**
     * Creates a list term with the specified list element and tail list.
     * This method does not check whether the tail list is actually a list.
     * @param element The first list element of the new list.
     * @param list The tail list of the new list.
     * @return A list term with the specified list element and tail list.
     */
    public static PrologTerm createList(final PrologTerm element, final PrologTerm list) {
        final List<PrologTerm> args = new ArrayList<PrologTerm>();
        args.add(element);
        args.add(list);
        return new PrologTerm(PrologBuiltin.LIST_CONSTRUCTOR_NAME, args);
    }

    /**
     * Creates a new true term.
     * @return A new true term.
     */
    public static PrologTerm createTrue() {
        return new PrologTerm(PrologBuiltin.TRUE_NAME);
    }

    public static PrologTerm createWitness(final FunctionSymbol sym) {
        final Set<String> used = java.util.Collections.singleton("X");
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_VARS);
        final List<PrologTerm> args = new ArrayList<PrologTerm>();
        for (int i = 0; i < sym.getArity(); i++) {
            args.add(new PrologNonAbstractVariable(fridge.getFreshName("X", false)));
        }
        return new PrologTerm(sym.getName(), args);
    }

    /**
     * @param unequalTerms
     * @param unequalTerms2
     * @return
     */
    public static boolean equalsModuloNonAbstractVariableRenaming(
        final Set<PrologTerm> terms1,
        final Set<PrologTerm> terms2)
    {
        if (terms1 == null) {
            return terms2 == null;
        } else if (terms2 == null) {
            return false;
        } else {
            boolean res = true;
            for (final PrologTerm t : terms1) {
                if (!res) {
                    break;
                }
                res &= PrologTerms.containsModuloNonAbstractVariableRenaming(t, terms2);
            }
            return res;
        }
    }

    public static PrologTerm flattenConjunction(final PrologTerm conjunction) {
        if (conjunction.isConjunction()) {
            final PrologTerm left = conjunction.getArgument(0);
            if (left.isConjunction()) {
                return PrologTerms.flattenConjunction(left.getArgument(0)).flatAppendConjunction(
                    PrologTerms.flattenConjunction(left.getArgument(1)).flatAppendConjunction(
                        PrologTerms.flattenConjunction(conjunction.getArgument(1))));
            } else {
                return PrologTerms.createConjunction(left, PrologTerms.flattenConjunction(conjunction.getArgument(1)));
            }
        }
        return conjunction;
    }

    public static PrologTerm getMaximum(final PrologTerm term1, final PrologTerm term2) {
        PrologTerm res = null;
        if (term1 == null && term2 == null) {
            return null;
        } else if (term1 == null) {
            res = term2;
        } else if (term2 == null) {
            res = term1;
        } else {
            res = term1.size() > term2.size() ? term1 : term2;
        }
        return res;
    }

    public static PrologTerm listAppend(final PrologTerm list1, final PrologTerm list2) {
        if (list1.isEmptyList()) {
            return list2;
        } else {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            args.add(list1.getArgument(0));
            args.add(PrologTerms.listAppend(list1.getArgument(1), list2));
            return new PrologTerm(PrologBuiltin.LIST_CONSTRUCTOR_NAME, args);
        }
    }

    /**
     * @param unify
     * @param unify2
     * @return
     */
    public static boolean retainAllModuloNonAbstractVariableRenaming(
        final Set<PrologTerm> set,
        final Set<PrologTerm> retainSet)
    {
        final Set<PrologTerm> delSet = new LinkedHashSet<PrologTerm>();
        for (final PrologTerm setTerm : set) {
            boolean in = false;
            for (final PrologTerm retainTerm : retainSet) {
                if (setTerm.equalsWithNonAbstractVariableNameChanging(retainTerm)) {
                    in = true;
                    break;
                }
            }
            if (!in) {
                delSet.add(setTerm);
            }
        }
        if (delSet.isEmpty()) {
            return false;
        } else {
            set.removeAll(delSet);
            return true;
        }
    }

    public static PrologTerm transformUnderscores(final PrologTerm term, final FreshNameGenerator fridge) {
        if (term == null) {
            return null;
        } else if (term.isUnderscore()) {
            return new PrologNonAbstractVariable(fridge.getFreshName("X", false));
        } else if (term.getArity() == 0) {
            return term;
        } else {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : term.getArguments()) {
                args.add(PrologTerms.transformUnderscores(arg, fridge));
            }
            return new PrologTerm(term.getName(), args);
        }
    }

    /**
     * Combines the replacements of the new argument MGU and the
     * current complete MGU and performs the replacements in the
     * terms immediately. Thus, clashes can be detected in the
     * replaced terms instead of different replacements in
     * argument MGUs.
     * @param term1
     * @param term2
     * @param i
     * @param mgu
     * @param res
     */
    private static Pair<PrologTerm, PrologTerm> combineMGUforArguments(
        PrologTerm term1,
        PrologTerm term2,
        final int i,
        final Map<PrologVariable, PrologTerm> mgu,
        final Map<PrologVariable, PrologTerm> res)
    {
        for (final Map.Entry<PrologVariable, PrologTerm> entry : mgu.entrySet()) {
            for (final Map.Entry<PrologVariable, PrologTerm> e : res.entrySet()) {
                res.put(e.getKey(), e.getValue().replaceAll(entry.getKey(), entry.getValue()));
            }
            res.put(entry.getKey(), entry.getValue());
            for (int j = i + 1; j < term1.getArity(); j++) {
                term1 = term1.replaceArgument(j, term1.getArgument(j).replaceAll(entry.getKey(), entry.getValue()));
                term2 = term2.replaceArgument(j, term2.getArgument(j).replaceAll(entry.getKey(), entry.getValue()));
            }
        }
        return new Pair<PrologTerm, PrologTerm>(term1, term2);
    }

}
