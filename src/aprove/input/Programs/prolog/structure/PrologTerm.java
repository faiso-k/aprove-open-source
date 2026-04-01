package aprove.input.Programs.prolog.structure;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.processors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * Class representing terms in Prolog. A PrologTerm has a name and a
 * list of arguments.<br><br>
 *
 * Created: Sep 8, 2006<br>
 * Last modified: Aug 19, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologTerm implements Exportable, HasName, PrettyStringable, Immutable, JSONExport {

    /**
     * @param name The term's identifier
     * @param args The arguments of this term. May be empty, but may not be null
     * @return A new Prolog term with the specified name and the given arguments.
     */
    public static PrologTerm create(String name, PrologTerm... args) {
        return new PrologTerm(name, Arrays.asList(args));
    }

    /**
     * The arguments of the root symbol. Also specifies its arity by the size of the list.
     */
    private final ImmutableList<PrologTerm> args;

    /**
     * The name of the root symbol.
     */
    private final String name;

    /**
     * Constructs a new PrologTerm with the specified name and an empty
     * list of arguments.
     * @param nameParam The term's identifier.
     */
    public PrologTerm(final String nameParam) {
        this(nameParam, null);
    }

    /**
     * Constructs a new PrologTerm with the specified name and arguments.
     * @param nameParam The term's identifier.
     * @param argsParam The term's arguments.
     */
    public PrologTerm(final String nameParam, final Collection<? extends PrologTerm> argsParam) {
        this(nameParam, argsParam == null ? new ArrayList<PrologTerm>() : new ArrayList<PrologTerm>(argsParam));
    }

    /**
     * Constructs a new PrologTerm with the specified name and list of
     * arguments.
     * @param nameParam The term's identifier.
     * @param argsParam The term's arguments.
     */
    public PrologTerm(final String nameParam, final List<PrologTerm> argsParam) {
        if (nameParam == null || "".equals(nameParam)) {
            throw new IllegalArgumentException("Name must not be null or empty!");
        }
        this.name = nameParam;
        if (argsParam == null) {
            this.args = ImmutableCreator.create(new ArrayList<PrologTerm>());
        } else {
            this.args = ImmutableCreator.create(argsParam);
        }
    }

    /**
     * Creates a new term where an argument is added to this term's list of
     * arguments at the specified position. The arguments at this position and
     * at all higher positions are shifted to one position higher.
     * @param index The position where the argument should be added.
     * @param term The argument to add.
     * @return A term with the specified argument added at the specified
     *         position.
     */
    public PrologTerm add(final int index, final PrologTerm term) {
        final List<PrologTerm> newArgs = new ArrayList<PrologTerm>(this.getArguments());
        newArgs.add(index, term);
        return new PrologTerm(this.getName(), newArgs);
    }

    /**
     * Creates a new PrologTerm where the specified term is appended to this
     * term's list of arguments.
     * @param term The argument to add.
     * @return A term with the additional specified argument.
     */
    public PrologTerm add(final PrologTerm term) {
        final List<PrologTerm> newArgs = new ArrayList<PrologTerm>(this.getArguments());
        newArgs.add(term);
        return new PrologTerm(this.getName(), newArgs);
    }

    /**
     * Applies the given substitution on this term.
     * This method is overridden in PrologVariable.
     * @param substitution The substitution to apply.
     * @return The substituted term.
     */
    public PrologTerm applySubstitution(final Map<? extends PrologVariable, ? extends PrologTerm> substitution) {
        if (this.isConstant()) {
            return this;
        } else {
            final List<PrologTerm> newArgs = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : this.getArguments()) {
                newArgs.add(arg.applySubstitution(substitution));
            }
            return new PrologTerm(this.getName(), newArgs);
        }
    }

    /**
     * Matches the current term to the specified one (without replacing abstract variables).
     * @param toMatch The term to match.
     * @return The matching substitution or null if the current term does not match the specified one.
     */
    public PrologSubstitution calculateMatcher(final PrologTerm toMatch) {
        return this.calculateMatcher(toMatch, false);
    }

    /**
     * Matches the current term to the specified one (with replacing abstract variables).
     * @param toMatch The term to match.
     * @return The matching substitution or null if the current term does not match the specified one.
     */
    public PrologSubstitution calculateMatcherWithAbstractVariables(final PrologTerm toMatch) {
        return this.calculateMatcher(toMatch, true);
    }

    /**
     * Calculates a most general unifier (MGU) for this term and the specified term. Returns null if the terms are not
     * unifiable. Uses the default settings in PrologTerms for the use of the occurs-check and the replacement
     * preference w.r.t. non-abstract variables.
     * @param toUnify The term to calculate a MGU for.
     * @return An MGU of this term and the specified term or null if the
     *         terms are not unifiable.
     */
    public PrologSubstitution calculateMGU(final PrologTerm toUnify) {
        return PrologTerms.calculateMGU(
            this,
            toUnify,
            PrologTerms.USE_OCCURS_CHECK,
            PrologTerms.PREFER_NONABSTRACT_REPLACEMENTS);
    }

    /**
     * @param toUnify
     * @param occursCheck
     * @return
     */
    public PrologSubstitution calculateMGU(final PrologTerm toUnify, final boolean occursCheck) {
        return PrologTerms.calculateMGU(this, toUnify, occursCheck, PrologTerms.PREFER_NONABSTRACT_REPLACEMENTS);
    }

    /**
     * @param toUnify
     * @param occursCheck
     * @param nonAbstractReplacementPreferred
     * @return
     */
    public PrologSubstitution calculateMGU(
        final PrologTerm toUnify,
        final boolean occursCheck,
        final boolean nonAbstractReplacementPreferred)
    {
        return PrologTerms.calculateMGU(this, toUnify, occursCheck, nonAbstractReplacementPreferred);
    }

    /**
     * @param toUnify
     * @param occursCheck
     * @param nonAbstractReplacementPreferred
     * @param fridge
     * @return
     */
    public PrologSubstitution calculateMGUwithOnlyFreshVariables(
        final PrologTerm toUnify,
        final boolean occursCheck,
        final boolean nonAbstractReplacementPreferred,
        final FreshNameGenerator fridge)
    {
        return PrologTerms.calculateMGUwithOnlyFreshVariables(
            this,
            toUnify,
            occursCheck,
            nonAbstractReplacementPreferred,
            new LinkedHashSet<PrologVariable>(),
            fridge);
    }

    /**
     * @param toUnify
     * @param occursCheck
     * @param nonAbstractReplacementPreferred
     * @param freshVars
     * @param fridge
     * @return
     */
    public PrologSubstitution calculateMGUwithOnlyFreshVariables(
        final PrologTerm toUnify,
        final boolean occursCheck,
        final boolean nonAbstractReplacementPreferred,
        final Set<PrologVariable> freshVars,
        final FreshNameGenerator fridge)
    {
        return PrologTerms.calculateMGUwithOnlyFreshVariables(
            this,
            toUnify,
            occursCheck,
            nonAbstractReplacementPreferred,
            freshVars,
            fridge);
    }

    /**
     * @param toUnify
     * @param occursCheck
     * @param fridge
     * @return
     */
    public PrologSubstitution calculateMGUwithOnlyFreshVariables(
        final PrologTerm toUnify,
        final boolean occursCheck,
        final FreshNameGenerator fridge)
    {
        return PrologTerms.calculateMGUwithOnlyFreshVariables(
            this,
            toUnify,
            occursCheck,
            PrologTerms.PREFER_NONABSTRACT_REPLACEMENTS,
            new LinkedHashSet<PrologVariable>(),
            fridge);
    }

    /**
     * @param toUnify
     * @param fridge
     * @return
     */
    public PrologSubstitution calculateMGUwithOnlyFreshVariables(
        final PrologTerm toUnify,
        final FreshNameGenerator fridge)
    {
        return PrologTerms.calculateMGUwithOnlyFreshVariables(
            this,
            toUnify,
            PrologTerms.USE_OCCURS_CHECK,
            PrologTerms.PREFER_NONABSTRACT_REPLACEMENTS,
            new LinkedHashSet<PrologVariable>(),
            fridge);
    }

    /**
     * Calculates a most general unifier (MGU) for this term and the
     * specified term. Returns null if the terms are not unifiable.
     * @param toUnify The term to calculate a MGU for.
     * @return A MGU of this term and the specified term or null if the
     *         terms are not unifiable.
     */
    public PrologSubstitution calculateMGUwithoutAbstractVariableUnification(final PrologTerm toUnify) {
        return PrologTerms.calculateMGUwithoutAbstractVariableUnification(this, toUnify, PrologTerms.USE_OCCURS_CHECK);
    }

    /**
     * @param toUnify
     * @param occursCheck
     * @return
     */
    public PrologSubstitution calculateMGUwithoutAbstractVariableUnification(
        final PrologTerm toUnify,
        final boolean occursCheck)
    {
        return PrologTerms.calculateMGUwithoutAbstractVariableUnification(this, toUnify, occursCheck);
    }

    /**
     * @param fridge
     */
    public Map<PrologNonAbstractVariable, PrologNonAbstractVariable> computeNonAbstractVarNameRefreshment(
        final FreshNameGenerator f)
    {
        final FreshNameGenerator fridge = f;
        final Map<PrologNonAbstractVariable, PrologNonAbstractVariable> toReplace =
            new LinkedHashMap<PrologNonAbstractVariable, PrologNonAbstractVariable>();
        this.walk(new TermWalker() {

            @Override
            public boolean goDeeper(final PrologTerm term) {
                return true;
            }

            @Override
            public boolean isApplicable(final PrologTerm term) {
                return term.isNonAbstractVariable();
            }

            @Override
            public void performAction(final PrologTerm term) {
                if (!toReplace.containsKey(term)) {
                    final PrologNonAbstractVariable newVar =
                        new PrologNonAbstractVariable(fridge.getFreshName("X", false));
                    toReplace.put((PrologNonAbstractVariable) term, newVar);
                }
            }

        });
        return toReplace;
    }

    /**
     * Returns the first conjunct of this PrologTerm if this
     * PrologTerm is a conjunction. Otherwise it will return null.
     * @return The first conjunct of this conjunction.
     */
    public PrologTerm conjunctionHead() {
        if (this.isConjunction()) {
            PrologTerm res = this.getArgument(0);
            while (res.isConjunction()) {
                res = res.getArgument(0);
            }
            return res;
        } else {
            return null;
        }
    }

    /**
     * Returns all but the first conjuncts of this
     * PrologTerm if this PrologTerm is a conjunction. Otherwise it
     * will return null.
     * @return A conjunction of all but the first conjuncts of this
     *         conjunction.
     */
    public PrologTerm conjunctionTail() {
        if (this.isConjunction()) {
            final PrologTerm left = this.getArgument(0);
            final PrologTerm right = this.getArgument(1);
            if (left.isConjunction()) {
                final PrologTerm leftTail = left.conjunctionTail();
                return PrologTerms.createConjunction(leftTail, right);
            } else {
                return right;
            }
        } else {
            return null;
        }
    }

    /**
     * Tests whether or not this term contains the specified term. A
     * term contains another term, if the first term or any of its
     * subterms are equal to the second term.
     * @param term The term to look for.
     * @return True, if this term contains the specified term.
     *         False otherwise.
     */
    public boolean contains(final PrologTerm term) {
        if (this.equals(term)) {
            return true;
        }
        for (final PrologTerm t : this.getArguments()) {
            if (t.contains(term)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns true iff this term contains a cut at a predication position.
     * @return True iff this term contains a cut at a predication position.
     */
    public boolean containsCut() {
        if (this.isCut()) {
            return true;
        } else if (this.isGoalJunctor()) {
            for (final PrologTerm arg : this.getArguments()) {
                if (arg.containsCut()) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Returns whether this term contains at least one non-abstract variable.
     * This method is overridden in PrologNonAbstractVariable.
     * @return True, if this term contains at least one non-abstract variable.
     *         False otherwise.
     */
    public boolean containsNonAbstractVariable() {
        for (final PrologTerm arg : this.getArguments()) {
            if (arg.containsNonAbstractVariable()) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether this term contains only variables from the specified set. This method is (and must be) overridden
     * in PrologVariable.
     * @param vars The set of variables.
     * @return True if the specified term only contains variables from the
     *         specified set
     */
    public boolean containsOnlyVariablesFrom(final Set<PrologVariable> vars) {
        for (final PrologTerm arg : this.getArguments()) {
            if (!arg.containsOnlyVariablesFrom(vars)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns a term where all abstract variables have been replaced by
     * non-abstract ones with the same names.
     * This method is overridden in PrologAbstractVariable.
     * @return A term where all abstract variables have been replaced by
     *         non-abstract ones with the same names.
     */
    public PrologTerm convertAbstractToNonAbstractVariables() {
        if (this.getArity() == 0) {
            return this;
        } else {
            final List<PrologTerm> newArgs = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : this.getArguments()) {
                newArgs.add(arg.convertAbstractToNonAbstractVariables());
            }
            return new PrologTerm(this.getName(), newArgs);
        }
    }

    /**
     * @return
     */
    public List<PrologTerm> createConjunctionListOfPredications() {
        return this.createConjunctionListOfPredications(new ArrayList<PrologTerm>());
    }

    /**
     * Creates a new FunctionSymbol from this term. The FunctionSymbol
     * has the name and arity of this term.
     * @return A new FunctionSymbol representing this term.
     */
    public FunctionSymbol createFunctionSymbol() {
        //TODO think about unsupporting this for variables
        return FunctionSymbol.create(this.getName(), this.getArity());
    }

    /**
     * @return
     */
    public List<Occurrence> createListOfPredicationPositions() {
        return this.createListOfPredicationPositions(new Occurrence());
    }

    /**
     * @return
     */
    public List<PrologTerm> createListOfPredications() {
        return this.createListOfPredications(new ArrayList<PrologTerm>());
    }

    /**
     * Creates a new set containing all abstract variables occurring in
     * this term. This method is overridden in PrologAbstractVariable.
     * @return A new set containing all abstract variables occurring in
     *         this term.
     */
    public Set<PrologAbstractVariable> createSetOfAllAbstractVariables() {
        final Set<PrologAbstractVariable> res = new LinkedHashSet<PrologAbstractVariable>();
        for (final PrologTerm term : this.getArguments()) {
            res.addAll(term.createSetOfAllAbstractVariables());
        }
        return res;
    }

    /**
     * Creates a new set containing all non-abstract variables occurring in
     * this term. This method is overridden in PrologNonAbstractVariable.
     * @return A new set containing all non-abstract variables occurring in
     *         this term.
     */
    public Set<PrologNonAbstractVariable> createSetOfAllNonAbstractVariables() {
        final Set<PrologNonAbstractVariable> res = new LinkedHashSet<PrologNonAbstractVariable>();
        for (final PrologTerm term : this.getArguments()) {
            res.addAll(term.createSetOfAllNonAbstractVariables());
        }
        return res;
    }

    /**
     * Creates a new set containing all variables used in this term.
     * This method is overridden in PrologVariable.
     * @return A new set containing all variables used in this term.
     */
    public VariableSet createSetOfAllVariables() {
        final VariableSet res = new VariableSet();
        for (final PrologTerm term : this.getArguments()) {
            res.addAll(term.createSetOfAllVariables());
        }
        return res;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object o) {
        if (o instanceof PrologTerm && o.hashCode() == this.hashCode()) {
            final PrologTerm t = (PrologTerm) o;
            if (t.getName().equals(this.getName()) && t.getArity() == this.getArity()) {
                boolean res = true;
                final List<PrologTerm> thisArgs = this.getArguments();
                final List<PrologTerm> otherArgs = t.getArguments();
                for (int i = 0; i < thisArgs.size(); i++) {
                    res &= thisArgs.get(i).equals(otherArgs.get(i));
                }
                return res;
            }
        }
        return false;
    }

    /**
     * @param t
     * @return
     */
    public boolean equalsWithNonAbstractVariableNameChanging(final PrologTerm t) {
        return this.equalsWithNonAbstractVarNameChanging(
            t,
            new LinkedHashMap<PrologNonAbstractVariable, PrologNonAbstractVariable>());
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.Exportable#export(aprove.verification.oldframework.Utility.Export_Util)
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();
        res.append(o.export(this.getName()));
        if (!this.isConstant() && !this.isVariable()) {
            res.append(o.export("("));
            for (int i = 0; i < this.getArity(); i++) {
                final PrologTerm t = this.getArgument(i);
                if (i > 0) {
                    res.append(o.export(", "));
                }
                res.append(t.export(o));
            }
            res.append(o.export(")"));
        }
        return res.toString();
    }

    /**
     * @param o
     * @param preds
     * @return
     */
    public String export(final Export_Util o, final Set<FunctionSymbol> preds) {
        final StringBuilder res = new StringBuilder();
        if (preds.contains(this.createFunctionSymbol())) {
            res.append(o.fontcolor(o.export(this.getName()), Color.BLUE));
        } else {
            res.append(o.export(this.getName()));
        }
        if (!this.isConstant() && !this.isVariable()) {
            res.append(o.export("("));
            for (int i = 0; i < this.getArity(); i++) {
                final PrologTerm t = this.getArgument(i);
                if (i > 0) {
                    res.append(o.export(", "));
                }
                res.append(t.export(o, preds));
            }
            res.append(o.export(")"));
        }
        return res.toString();
    }

    /**
     * @param conjunction
     * @return
     */
    public PrologTerm flatAppendConjunction(final PrologTerm conjunction) {
        if (this.isConjunction()) {
            return PrologTerms.createConjunction(
                this.getArgument(0),
                this.getArgument(1).flatAppendConjunction(conjunction));
        } else {
            return PrologTerms.createConjunction(this, conjunction);
        }
    }

    /**
     * @return
     */
    public PrologTerm flattenOutConjunctions() {
        if (this.isGoalJunctor()) {
            if (this.isConjunction()) {
                return PrologTerms.flattenConjunction(this);
            } else {
                final List<PrologTerm> args = new ArrayList<PrologTerm>();
                args.add(this.getArgument(0).flattenOutConjunctions());
                args.add(this.getArgument(1).flattenOutConjunctions());
                return new PrologTerm(this.getName(), args);
            }
        } else {
            return this;
        }
    }

    /**
     * @param names
     */
    public void getAllNames(final Set<String> names) {
        names.add(this.getName());
        for (final PrologTerm arg : this.getArguments()) {
            arg.getAllNames(names);
        }
    }

    /**
     * Creates a set containing all positions of variables in this term.
     * This method is overridden in PrologVariable.
     * @return A set containing all positions of variables in this term.
     */
    public Set<Occurrence> getAllOccurrencesOfVariables() {
        final Set<Occurrence> res = new LinkedHashSet<Occurrence>();
        for (int i = 0; i < this.getArity(); i++) {
            final Set<Occurrence> resForArg = this.getArgument(i).getAllOccurrencesOfVariables();
            for (final Occurrence occ : resForArg) {
                res.add(occ.addChildNumberInFront(i));
            }
        }
        return res;
    }

    /**
     * Returns the term's argument at the specified position.
     * @param index The argument's position.
     * @return The term's argument at the specified position.
     * @throws IndexOutOfBoundsException If the index is out of bounds.
     */
    public PrologTerm getArgument(final int index) {
        return this.getArguments().get(index);
    }

    /**
     * Returns the term's list of arguments.
     * @return The term's arguments.
     */
    public ImmutableList<PrologTerm> getArguments() {
        return this.args;
    }

    /**
     * Returns the term's arity.
     * @return The term's arity.
     */
    public int getArity() {
        return this.getArguments().size();
    }

    /**
     * Returns the term's identifier.
     * @return The term's identifier.
     */
    @Override
    public String getName() {
        return this.name;
    }

    /**
     * Returns a set containing all Occurrences of the specified
     * subterm in this term.
     * @param subterm The subterm to find in this term.
     * @return A set containing all Occurrences of subterm in this term.
     */
    public Set<Occurrence> getOccurrences(final PrologTerm subterm) {
        return Occurrence.getOccurrences(this, subterm);
    }

    /**
     * @return
     */
    public String getPrettyName() {
        final StringBuilder res = new StringBuilder();
        final char[] string = this.getName().toCharArray();
        for (final char c : string) {
            if (c == '\\') {
                res.append(c);
                res.append(c);
            } else {
                res.append(c);
            }
        }
        return res.toString();
    }

    /**
     * Returns the subterm at the specified Occurrence of this term.
     * @param occ The Occurrence of the subterms.
     * @return The subterm at the specified Occurrence of this term.
     */
    public PrologTerm getSubterm(final Occurrence occ) {
        PrologTerm res = this;
        for (final Integer i : occ) {
            if (res.getArity() > i) {
                res = res.getArgument(i);
            } else {
                return null;
            }
        }
        return res;
    }

    /**
     * @param sym
     * @return
     */
    public List<PrologTerm> getSubtermsWithFunctionSymbol(final FunctionSymbol sym) {
        final List<PrologTerm> res = new ArrayList<PrologTerm>();
        this.getSubtermsWithFunctionSymbol(sym, res);
        return res;
    }

    /**
     * Returns true iff this term contains a disjunction which is not part of an if-then-else construct.
     * @return True iff this term contains a disjunction which is not part of an if-then-else construct.
     */
    public boolean hasDisjunction() {
        if (this.isDisjunctionTerm() && !this.getArgument(0).isIf()) {
            return true;
        } else {
            for (final PrologTerm arg : this.getArguments()) {
                if (arg.hasDisjunction()) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Tests whether or not the specified FunctionSymbol has the same
     * name and arity as this term.
     * @param sym The predicate to match.
     * @return True, if the specified predicate matches this term.
     */
    public boolean hasEqualFunctionSymbol(final FunctionSymbol sym) {
        return this.getName().equals(sym.getName()) && this.getArity() == sym.getArity();
    }

    /**
     * Tests whether or not the specified PrologTerm has the same name
     * and arity as this term.
     * @param t The PrologTerm to match.
     * @return True, if the specified PrologTerm matches this term.
     */
    public boolean hasEqualFunctionSymbol(final PrologTerm t) {
        return t.getName().equals(this.getName()) && t.getArity() == this.getArity();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        int sum = 0;
        for (int i = 0; i < this.getArity(); i++) {
            sum += this.getArgument(i).hashCode();
        }
        return 5 * this.getName().hashCode() + 3 * sum;
    }

    /**
     * Tests whether or not this PrologTerm is an abstract variable
     * used in termination graphs.
     * This method is overriden in PrologAbstractVariable.
     * @return True, if this term is an instance of
     *         PrologAbstractVariable. False otherwise.
     */
    public boolean isAbstractVariable() {
        return false;
    }

    /**
     * Tests whether or not this term is an atom. A term is an atom, if
     * it is neither a variable nor a number, it's root symbol is a predicate
     * symbol, and all of its arguments are constructor terms.
     * To tell constructors from predicates, a set of all prediactes
     * must be specified for this method.
     * This method is overridden in PrologVariable and PrologNumber.
     * @param preds A set of all predicates.
     * @return True, if this term is an atom. False otherwise.
     */
    public boolean isAtom(final Set<FunctionSymbol> preds) {
        if (preds.contains(this.createFunctionSymbol())) {
            for (final PrologTerm term : this.getArguments()) {
                if (term.isCompound()) {
                    if (preds.contains(term.createFunctionSymbol())) {
                        return false;
                    } else {
                        for (final PrologTerm arg : term.getArguments()) {
                            if (!arg.isConstructorTerm(preds)) {
                                return false;
                            }
                        }
                        return true;
                    }
                }
            }
            return true;
        } else {
            return false;
        }
    }

    /**
     * @return
     */
    public boolean isCall() {
        return this.getName().equals(PrologBuiltin.CALL_NAME) && this.getArity() == 1;
    }

    /**
     * Returns whether or not the term is a compound term. A term is
     * compound, if its list of arguments is not empty.
     * @return True, if the term is compound. False otherwise.
     */
    public boolean isCompound() {
        return !this.getArguments().isEmpty();
    }

    /**
     * Tests whether or not this term is a conjunction, i.e. its name is
     * PrologBuiltin.CONJUNCTION_NAME and its arity is 2.
     * @return True, if this term is a conjunction. False otherwise.
     */
    public boolean isConjunction() {
        return this.getName().equals(PrologBuiltin.CONJUNCTION_NAME) && this.getArity() == 2;
    }

    /**
     * Tests whether or not this term is a conjuction list of atoms, i.e.
     * it is an atom or it is a conjunction and its first argument is an
     * atom while its second argument is a conjunction of atoms. To tell
     * constructors from predicates a set of all predicates must be
     * specified for this method.
     * @param preds A set of all predicates.
     * @return True, if this term is a conjunction of atoms.
     *         False otherwise.
     */
    public boolean isConjunctionListOfAtoms(final Set<FunctionSymbol> preds) {
        return this.isAtom(preds)
            || (this.isConjunction() && this.getArgument(0).isAtom(preds) && this
                .getArgument(1)
                .isConjunctionListOfAtoms(preds));
    }

    /**
     * @return
     */
    public boolean isConjunctionOfTrue() {
        if (this.isConjunction()) {
            return this.getArgument(0).isConjunctionOfTrue() && this.getArgument(1).isConjunctionOfTrue();
        } else {
            return this.isTrue();
        }
    }

    /**
     * Returns whether or not the term is constant. A term is constant,
     * if its list of arguments is empty and it is no variable.
     * This method is overridden in PrologVariable.
     * @return True, if the term is constant. False otherwise.
     */
    public boolean isConstant() {
        return this.getArguments().isEmpty();
    }

    /**
     * Tests whether or not this term is a constructor term. A term is a
     * constructor term, if it contains no predicates. To tell
     * constructors from predicates, a set of all predicates must be
     * specified for this method. A non-abstract variable is considered a
     * constructor term while an abstract one is not.
     * This method is overridden in PrologVariable and PrologAbstractVariable.
     * @param preds A set of all predicates.
     * @return True, if this term is a constructor term. False otherwise.
     */
    public boolean isConstructorTerm(final Set<FunctionSymbol> preds) {
        if (preds.contains(this.createFunctionSymbol())) {
            return false;
        }
        for (final PrologTerm arg : this.getArguments()) {
            if (!arg.isConstructorTerm(preds)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Tests whether or not this term is a cut.
     * This method is overridden in LabeledCut.
     * @return True, if this term is a cut. False otherwise.
     */
    public boolean isCut() {
        return this.getName().equals(PrologBuiltin.CUT_NAME) && this.getArity() == 0;
    }

    /**
     * @return
     */
    public boolean isCyclic() {
        if (this instanceof PrologCyclicTerm) {
            return true;
        } else {
            for (final PrologTerm t : this.getArguments()) {
                if (t.isCyclic()) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Tests whether or not this term is a disjunction term (it does not check
     * whether it belongs to an if-then-else construct).
     * @return True, if this term is a disjunction term. False otherwise.
     */
    public boolean isDisjunctionTerm() {
        return this.getName().equals(PrologBuiltin.DISJUNCTION_NAME) && this.getArity() == 2;
    }

    /**
     * @return
     */
    public boolean isEmptyList() {
        return this.getName().equals(PrologBuiltin.EMPTY_LIST_CONSTRUCTOR_NAME) && this.getArity() == 0;
    }

    /**
     * Tests whether or not this term is a fail term.
     * @return True, if this term is a fail term. False otherwise.
     */
    public boolean isFail() {
        return this.getName().equals(PrologBuiltin.FAIL_NAME) && this.getArity() == 0;
    }

    /**
     * @return
     */
    public boolean isFiniteList() {
        if (this.isEmptyList()) {
            return true;
        } else if (this.isList()) {
            return this.getArgument(1).isFiniteList();
        } else {
            return false;
        }
    }

    /**
     * Tests whether or not this term is a >= term.
     * @return True, if this term is a >= term. False otherwise.
     */
    public boolean isGeq() {
        return this.getName().equals(PrologBuiltin.GEQ_NAME) && this.getArity() == 2;
    }

    /**
     * @return
     */
    public boolean isGoalJunctor() {
        return this.isConjunction() || this.isDisjunctionTerm() || this.isIf();
    }

    /**
     * Tests whether or not this term is a > term.
     * @return True, if this term is a > term. False otherwise.
     */
    public boolean isGreater() {
        return this.getName().equals(PrologBuiltin.GREATER_NAME) && this.getArity() == 2;
    }

    /**
     * Checks whether or not this term is a ground term, i.e. it
     * contains no variables.
     * This method is overridden in PrologVariable.
     * @return True, if this term is a ground term. False otherwise.
     */
    public boolean isGround() {
        for (final PrologTerm t : this.getArguments()) {
            if (!t.isGround()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Tests whether or not this term is an if term.
     * @return True, if this term is an if term. False otherwise.
     */
    public boolean isIf() {
        return this.getName().equals(PrologBuiltin.IF_NAME) && this.getArity() == 2;
    }

    /**
     * Tests whether or not this term is an integer.
     * This method is overridden in PrologInt.
     * @return True, if this term is an integer. False otherwise.
     */
    public boolean isInt() {
        return false;
    }

    /**
     * Tests whether or not this term is an is term.
     * @return True, if this term is an is term. False otherwise.
     */
    public boolean isIs() {
        return this.getName().equals(PrologBuiltin.IS_NAME) && this.getArity() == 2;
    }

    /**
     * Tests whether or not this term is a =:= term.
     * @return True, if this term is a =:= term. False otherwise.
     */
    public boolean isIsEqual() {
        return this.getName().equals(PrologBuiltin.ISEQUAL_NAME) && this.getArity() == 2;
    }

    /**
     * Tests whether or not this term is a =\= term.
     * @return True, if this term is a =\= term. False otherwise.
     */
    public boolean isIsUnequal() {
        return this.getName().equals(PrologBuiltin.ISUNEQUAL_NAME) && this.getArity() == 2;
    }

    /**
     * Tests whether or not this term is a =< term.
     * @return True, if this term is a =< term. False otherwise.
     */
    public boolean isLeq() {
        return this.getName().equals(PrologBuiltin.LEQ_NAME) && this.getArity() == 2;
    }

    /**
     * Tests whether or not this term is a < term.
     * @return True, if this term is a < term. False otherwise.
     */
    public boolean isLess() {
        return this.getName().equals(PrologBuiltin.LESS_NAME) && this.getArity() == 2;
    }

    /**
     * Tests whether or not this term is a list. A term is a list, if its
     * name is PrologPredefined.LIST_CONSTRUCTOR_NAME and its arity is 2 or
     * if it is the empty list ([]).
     * @return True, if this term is a list. False otherwise.
     */
    public boolean isList() {
        return (this.getName().equals(PrologBuiltin.LIST_CONSTRUCTOR_NAME) && this.getArity() == 2)
            || this.isEmptyList();
    }

    /**
     * Tests whether or not this term is a list of constructor terms, i.e. it
     * is a list and contains no predicates. To tell constructors from
     * predicates, a set of all predicates must be specified for this method.
     * @param preds A set of all predicates.
     * @return True, if this term is a constant list. False otherwise.
     */
    public boolean isListOfConstructorTerms(final Set<FunctionSymbol> preds) {
        if (this.isList()) {
            return this.getArgument(0).isConstructorTerm(preds) && this.getArgument(1).isListOfConstructorTerms(preds);
        } else {
            return false;
        }
    }

    /**
     * Tests whether or not this PrologTerm is a non-abstract variable.
     * This method is overriden in PrologNonAbstractVariable.
     * @return True, if this term is an instance of
     *         PrologNonAbstractVariable. False otherwise.
     */
    public boolean isNonAbstractVariable() {
        return false;
    }

    /**
     * @return
     */
    public boolean isNot() {
        return this.getName().equals(PrologBuiltin.NOT_NAME) && this.getArity() == 1;
    }

    /**
     * Tests whether or not this term is a number, i.e. it is an integer,
     * float or a symbol for infinity or nan(<b>n</b>ot <b>a n</b>umber).
     * This method is overridden in PrologNumber.
     * @return True, if this term is a number. False otherwise.
     */
    public boolean isNumber() {
        return false;
    }

    /**
     * Tests whether or not this term is true term.
     * @return True, if this term is a true term.
     */
    public boolean isTrue() {
        return this.getName().equals(PrologBuiltin.TRUE_NAME) && this.getArity() == 0;
    }

    /**
     * Tests whether or not this term is an anonymous variable.
     * This method is overridden in PrologNonAbstractVariable.
     * @return True, if this term is an anonymous variable. False otherwise.
     */
    public boolean isUnderscore() {
        return false;
    }

    /**
     * Returns whether or not this term is a variable.
     * This method is overridden in PrologVariable.
     * @return True, if this term is a variable. False otherwise.
     */
    public boolean isVariable() {
        return false;
    }

    /**
     * @param toMatch
     * @return
     */
    public boolean matches(final PrologTerm toMatch) {
        return this.calculateMatcher(toMatch) != null;
    }

    /**
     * @param toMatch
     * @return
     */
    public boolean matchesWithAbstractVariables(final PrologTerm toMatch) {
        return this.calculateMatcherWithAbstractVariables(toMatch) != null;
    }

    /**
     * Returns a term where all non-abstract variables have been freshly
     * renamed using the specified FreshNameGenerator.
     * @param fridge The FreshNameGenerator to use.
     * @return A term where all non-abstract variables have been freshly
     *         renamed
     */
    public PrologTerm nonAbstractVarsRefreshed(final FreshNameGenerator fridge) {
        return this.applySubstitution(this.computeNonAbstractVarNameRefreshment(fridge));
    }

    /**
     * Tests whether or not a subterm with the specified function symbol
     * occurs in this term.
     * @param symbol The subterm's function symbol.
     * @return True, if a subterm with the specified function symbol
     *         occurs in this term. False otherwise.
     */
    public boolean occurs(final FunctionSymbol symbol) {
        return this.occurs(symbol.getName(), symbol.getArity());
    }

    /**
     * Tests whether or not the specified term occurs anywhere in this
     * term. That means this method returns true, if this term or any of
     * its subterms match the specified term in the way that it has the
     * same name and arity.
     * @param term The term to look for.
     * @return True, if this term or any of its subterms match the
     *         specified term. False otherwise.
     */
    public boolean occurs(final PrologTerm term) {
        if (this.hasEqualFunctionSymbol(term)) {
            return true;
        }
        for (final PrologTerm t : this.getArguments()) {
            if (t.occurs(term)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Tests whether or not a subterm with the specified name occurs in
     * this term. The subterm's arity is arbitrary.
     * @param name The name to look for.
     * @return True, if a subterm with the specified name occurs in this
     *         term. False otherwise.
     */
    public boolean occurs(final String name) {
        if (this.getName().equals(name)) {
            return true;
        }
        for (final PrologTerm t : this.getArguments()) {
            if (t.occurs(name)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Tests whether or not a subterm with the specified name and arity
     * occurs in this term.
     * @param name The subterm's name.
     * @param arity The subterm's arity.
     * @return True, if a subterm with the specified name and arity
     *         occurs in this term. False otherwise.
     */
    public boolean occurs(final String name, final int arity) {
        if (this.getName().equals(name) && this.getArity() == arity) {
            return true;
        }
        for (final PrologTerm t : this.getArguments()) {
            if (t.occurs(name)) {
                return true;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.Graph.PrettyStringable#prettyToString()
     */
    @Override
    public String prettyToString() {
        final StringBuilder res = new StringBuilder();
        if (this.isConstant() || this.isVariable()) {
            res.append(this.getPrettyName());
        } else {
            res.append(this.getPrettyName());
            res.append("(");
            for (int i = 0; i < this.getArity(); i++) {
                final PrologTerm t = this.getArgument(i);
                if (i > 0) {
                    res.append(", ");
                }
                res.append(t.prettyToString());
            }
            res.append(")");
        }
        return res.toString();
    }

    /**
     * Renames every term with the same function symbol as oldTerm by the name
     * of newTerm. If the arity of newTerm does not match the arity of oldTerm,
     * this method will return this term unchanged.
     * @param oldTerm The PrologTerm to be renamed.
     * @param newTerm The PrologTerm with the new name.
     */
    public PrologTerm rename(final PrologTerm oldTerm, final PrologTerm newTerm) {
        if (oldTerm.getArity() != newTerm.getArity()) {
            return this;
        } else {
            return this.rename(oldTerm.getName(), newTerm.getName(), newTerm.getArity());
        }
    }

    /**
     * Renames every term which matches oldTerm with newName.
     * @param oldTerm The PrologTerm to be renamed.
     * @param newName The term's new name.
     */
    public PrologTerm rename(final PrologTerm oldTerm, final String newName) {
        return this.rename(oldTerm.getName(), newName, oldTerm.getArity());
    }

    /**
     * Replaces the name of every PrologTerm whose arity matches arity
     * and whose name matches oldName with newName.
     * This method is overridden in PrologVariable, PrologNumber and their
     * subclasses.
     * @param oldName The name to be replaced.
     * @param newName The name to replace.
     * @param arity The arity of the PrologTerm to be renamed.
     */
    public PrologTerm rename(final String oldName, final String newName, final int arity) {
        if (this.getArity() == arity && this.getName().equals(oldName)) {
            return new PrologTerm(newName, this.getArguments());
        } else if (this.isConstant()) {
            return this;
        } else {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            for (final PrologTerm t : this.getArguments()) {
                args.add(t.rename(oldName, newName, arity));
            }
            return new PrologTerm(this.getName(), args);
        }
    }

    /**
     * Renames non-abstract variables from X_1 to X_n using the specified
     * renaming map.
     * This method is overridden in PrologNonAbstractVariable.
     * @param renaming The map used for the renaming. It will be modified by
     *                 this method.
     * @return A variable-renamed term.
     */
    public PrologTerm renameNonAbstractVariablesCanonically(
        final Map<PrologNonAbstractVariable, PrologNonAbstractVariable> renaming)
    {
        if (this.isConstant()) {
            return this;
        } else {
            final List<PrologTerm> newArgs = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : this.getArguments()) {
                newArgs.add(arg.renameNonAbstractVariablesCanonically(renaming));
            }
            return new PrologTerm(this.getName(), newArgs);
        }
    }

    /**
     * Returns a term where the subterm at the specified position has been
     * replaced by the specified term.
     * @param term The new subterm.
     * @param occ The new subterm's position.
     * @return A term where the subterm at the specified position has been
     *         replaced by the specified term.
     */
    public PrologTerm replace(final PrologTerm term, final Occurrence occ) {
        if (occ.isEpsilon()) {
            return term;
        } else {
            final List<PrologTerm> newArgs = new ArrayList<PrologTerm>(this.getArguments());
            newArgs.set(
                occ.getChildNumber(0),
                this.getArgument(occ.getChildNumber(0)).replace(term, occ.getDirectSubOccurrence()));
            return new PrologTerm(this.getName(), newArgs);
        }
    }

    /**
     * Replaces all occurrences of oldTerm in this term's subterms
     * with newTerm. If oldTerm is a subterm of newTerm this method will
     * not replace occurrences of oldTerm in already replaced terms,
     * because the replacement would not terminate then.
     * This method is overridden in PrologVariable.
     * @param oldTerm The subterm to be replaced.
     * @param newTerm The term to replace.
     * @return The term where all occurrences of oldTerm are replaced by
     *         newTerm.
     */
    public PrologTerm replaceAll(final PrologTerm oldTerm, final PrologTerm newTerm) {
        if (this.equals(oldTerm)) {
            return newTerm;
        } else if (this.isConstant()) {
            return this;
        } else {
            final List<PrologTerm> newArgs = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : this.getArguments()) {
                newArgs.add(arg.replaceAll(oldTerm, newTerm));
            }
            return new PrologTerm(this.getName(), newArgs);
        }
    }

    /**
     * Creates a term where the argument at the specified position is set to
     * the specified term.
     * @param index The argument's position.
     * @param term The term to set.
     * @return The term where the argument at the specified position is set to
     * the specified term.
     */
    public PrologTerm replaceArgument(final int index, final PrologTerm term) {
        final List<PrologTerm> newArgs = new ArrayList<PrologTerm>(this.getArguments());
        newArgs.set(index, term);
        return new PrologTerm(this.getName(), newArgs);
    }

    /**
     * Creates a new term with the same arguments, but the specified identifier.
     * This method is overridden in PrologNumber, PrologVariable and their
     * subclasses.
     * @param nameParam The term's new identifier.
     * @return A new term with the same arguments, but the specified identifier.
     */
    public PrologTerm replaceName(final String nameParam) {
        return new PrologTerm(nameParam, this.getArguments());
    }

    /**
     * Replaces every call to a predicate from the specified collection by the
     * specified term. Variables or numbers are not replaced. This method is
     * overridden in PrologVariable and PrologNumber.
     * @param preds The predicates which should be replaced.
     * @param term The term by which the predicates should be replaced.
     * @return A new PrologTerm where all specified predicate calls are
     *         replaced by the specified term.
     */
    public PrologTerm replacePredicates(final Collection<? extends FunctionSymbol> preds, final PrologTerm term) {
        if (preds.contains(this.createFunctionSymbol())) {
            return term;
        } else {
            final List<PrologTerm> newArgs = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : this.getArguments()) {
                newArgs.add(arg.replacePredicates(preds, term));
            }
            return new PrologTerm(this.getName(), newArgs);
        }
    }

    /**
     * Returns the this term's size, i.e., the number of positions inside this
     * term.
     * @return The size of this term.
     */
    public int size() {
        int res = 1;
        for (int i = 0; i < this.getArity(); i++) {
            res += this.getArgument(i).size();
        }
        return res;
    }

    /**
     * @param negate Flag indicating whether the comparison should be negated.
     * @param pd The map containing the symbols for ITRSs - or whatever...
     * @return An ITerm representation of the comparison represented by the current PrologTerm.
     */
    public ITerm<BigInt> toComparisonTerm(final boolean negate, final IDPPredefinedMap pd) {
        final FunctionSymbol sym = this.createFunctionSymbol();
        if (Globals.useAssertions) {
            assert (PrologBuiltins.ARITHMETIC_COMPARISON_PREDICATES.contains(sym)) : "Unkown arithmetic comparison operator!";
        }
        if (sym.equals(PrologBuiltin.ISEQUAL_PREDICATE)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(
                    negate ? PredefinedFunction.Func.Neq : PredefinedFunction.Func.Eq,
                    DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.ISUNEQUAL_PREDICATE)) {
            return ITerm.<BigInt>createFunctionApplication(pd.<BigInt>getFunctionSymbolChecked(negate
                ? PredefinedFunction.Func.Eq
                    : PredefinedFunction.Func.Neq, DomainFactory.INTEGER_INTEGER), this
                .getArgument(0)
                .toEvaluationTerm(pd), this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.GEQ_PREDICATE)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(
                    negate ? PredefinedFunction.Func.Lt : PredefinedFunction.Func.Ge,
                    DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.GREATER_PREDICATE)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(
                    negate ? PredefinedFunction.Func.Le : PredefinedFunction.Func.Gt,
                    DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.LEQ_PREDICATE)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(
                    negate ? PredefinedFunction.Func.Gt : PredefinedFunction.Func.Le,
                    DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.LESS_PREDICATE)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(
                    negate ? PredefinedFunction.Func.Ge : PredefinedFunction.Func.Lt,
                    DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        }
        return null;
    }

    /**
     * @param variable
     * @return
     */
    public PrologTerm toCyclic(final PrologVariable variable) {
        return new PrologCyclicTerm(this, variable);
    }

    /**
     * @param pd The map containing the symbols for ITRSs - or whatever...
     * @return An ITerm representation of the evaluation represented by the current PrologTerm.
     */
    public ITerm<BigInt> toEvaluationTerm(final IDPPredefinedMap pd) {
        final FunctionSymbol sym = this.createFunctionSymbol();
        if (Globals.useAssertions) {
            assert (PrologBuiltins.ARITHMETIC_OPERATORS.contains(sym)) : "Unkown arithmetic operator!";
        }
        if (sym.equals(PrologBuiltin.PLUS_SYMBOL)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(PredefinedFunction.Func.Add, DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.MINUS_SYMBOL)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(PredefinedFunction.Func.Sub, DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.TIMES_SYMBOL)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(PredefinedFunction.Func.Mul, DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.INTDIV_SYMBOL)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(PredefinedFunction.Func.Div, DomainFactory.INTEGER_INTEGER),
                this.getArgument(0).toEvaluationTerm(pd),
                this.getArgument(1).toEvaluationTerm(pd));
        } else if (sym.equals(PrologBuiltin.POSITIVE_SIGN)) {
            return this.getArgument(0).toEvaluationTerm(pd);
        } else if (sym.equals(PrologBuiltin.NEGATIVE_SIGN)) {
            return ITerm.<BigInt>createFunctionApplication(
                pd.<BigInt>getFunctionSymbolChecked(PredefinedFunction.Func.Sub, DomainFactory.INTEGER_INTEGER),
                pd.createIntIntTerm(BigInt.create(BigInteger.ZERO), DomainFactory.INTEGERS),
                this.getArgument(0).toEvaluationTerm(pd));
        }
        return null;
    }

    @Override
    public Object toJSON() {
        return this.toSExpression();
    }

    public String toLaTeX(final KnowledgeBase kb) {
        if (this.getArity() == 0) {
            if (this.isCut()) {
                return "\\Fcut";
            } else if (this.isEmptyList()) {
                return "\\FemptyList";
            } else {
                return "\\F" + this.getName();
            }
        }
        final StringBuilder res = new StringBuilder();
        if (this.isConjunction()) {
            res.append(this.getArgument(0).toLaTeX(kb));
            res.append(",");
            res.append(this.getArgument(1).toLaTeX(kb));
        } else {
            res.append("\\F");
            res.append(PrologBuiltins.toLaTeX(this.getName()));
            res.append("(");
            boolean first = true;
            for (final PrologTerm arg : this.getArguments()) {
                if (first) {
                    first = false;
                } else {
                    res.append(",");
                }
                res.append(arg.toLaTeX(kb));
            }
            res.append(")");
        }
        return res.toString();
    }

    /**
     * @return This term as an s-expression.
     */
    public String toSExpression() {
        StringBuilder res = new StringBuilder();
        res.append("(");
        res.append(this.name);
        for (PrologTerm arg : this.args) {
            res.append(" ");
            res.append(arg.toSExpression());
        }
        res.append(")");
        return res.toString();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        if (this.isConstant() || this.isVariable()) {
            res.append(this.getName());
        } else {
            res.append(this.getName());
            res.append("(");
            for (int i = 0; i < this.getArity(); i++) {
                final PrologTerm t = this.getArgument(i);
                if (i > 0) {
                    res.append(", ");
                }
                res.append(t.toString());
            }
            res.append(")");
        }
        return res.toString();
    }

    /**
     * Transforms this PrologTerm into a Term used in the DPFramework.
     * This method is overridden in PrologVariable.
     * @return A term from the DPFramework corresponding to this PrologTerm.
     */
    public TRSTerm toTerm() {
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        for (final PrologTerm arg : this.getArguments()) {
            newArgs.add(arg.toTerm());
        }
        return TRSTerm.createFunctionApplication(this.createFunctionSymbol(), newArgs);
    }

    /**
     * Transforms this PrologTerm into a freshly renamed Term used in the
     * DPFramework. This method is overridden in PrologVariable.
     * @param fridge Fresh names come out of the fridge...
     * @return A freshly renamed term from the DPFramework corresponding to
     *         this PrologTerm.
     */
    public TRSTerm toTerm(final PrologFNG fridge) {
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        for (final PrologTerm arg : this.getArguments()) {
            newArgs.add(arg.toTerm(fridge));
        }
        return TRSTerm.createFunctionApplication(
            FunctionSymbol.create(fridge.getFreshName(this.getName(), true), this.getArity()),
            newArgs);
    }

    /**
     * @return
     */
    public PrologTerm trimTruesInConjunction() {
        if (this.isConjunction()) {
            final PrologTerm reduced1 = this.getArgument(0).reduceTruesInConjunction();
            final PrologTerm reduced2 = this.getArgument(1).reduceTruesInConjunction();
            if (reduced1 == null && reduced2 == null) {
                return null;
            } else if (reduced1 == null) {
                return reduced2;
            } else if (reduced2 == null) {
                return reduced1;
            } else {
                return PrologTerms.createConjunction(reduced1, reduced2);
            }
        } else {
            return this;
        }
    }

    /**
     * Test whether or not this term is unifiable with the specified
     * term.
     * @param term The term with which this term should be unifiable.
     * @return True, if this term is unifiable with the specified term.
     *         False otherwise.
     */
    public boolean unifiesWith(final PrologTerm term) {
        return this.calculateMGU(term) != null;
    }

    /**
     * This method implements the visitor pattern for ReplacementWalkers.
     * It is overridden in PrologNumber and PrologVariable.
     * @param walker The visitor.
     * @return The replaced term.
     */
    public PrologTerm walk(final ReplacementWalker walker) {
        if (walker.isApplicable(this)) {
            return walker.replace(this);
        } else if (walker.goDeeper(this)) {
            final List<PrologTerm> newArgs = new ArrayList<PrologTerm>();
            for (final PrologTerm term : this.getArguments()) {
                newArgs.add(term.walk(walker));
            }
            return new PrologTerm(this.getName(), newArgs);
        } else {
            return this;
        }
    }

    /**
     * Method for using a TermWalker on this term. This method will pass
     * the TermWalker through this term and its subterms using its
     * goDeeper() and isApplicable() methods and calling the
     * performAction() method on applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walk(final TermWalker walker) {
        if (walker.isApplicable(this)) {
            walker.performAction(this);
        }
        if (walker.goDeeper(this)) {
            for (final PrologTerm term : this.getArguments()) {
                term.walk(walker);
            }
        }
    }

    /**
     * Method for using a TermWalker on the conjunctions in this term.
     * This method will pass the TermWalker through the conjuncted terms
     * calling the performAction() method on applicable (sub-)terms.
     * @param walker The TermWalker to use.
     */
    public void walkConjunction(final TermWalker walker) {
        if (this.isConjunction()) {
            this.getArgument(0).walkConjunction(walker);
            this.getArgument(1).walkConjunction(walker);
        } else {
            this.walk(walker);
        }
    }

    /**
     * @param walker
     */
    public void walkPredication(final TermWalker walker) {
        if (this.isGoalJunctor()) {
            this.getArgument(0).walkPredication(walker);
            this.getArgument(1).walkPredication(walker);
        } else {
            this.walk(walker);
        }
    }

    /**
     * @param toMatch
     * @param withAbstract
     * @return
     */
    private PrologSubstitution calculateMatcher(final PrologTerm toMatch, final boolean withAbstract) {
        final PrologSubstitution matcher = new PrologSubstitution();
        if (this.equals(toMatch)) {
            return matcher;
        } else if ((withAbstract && this.isVariable()) || this.isNonAbstractVariable()) {
            matcher.put((PrologVariable) this, toMatch);
            return matcher;
        } else if (this.getName().equals(toMatch.getName()) && this.getArity() == toMatch.getArity()) {
            for (int i = 0; i < this.getArity(); i++) {
                final Map<PrologVariable, PrologTerm> argMatcher =
                    this.getArgument(i).calculateMatcher(toMatch.getArgument(i), withAbstract);
                if (argMatcher == null) {
                    return null;
                } else {
                    for (final Map.Entry<PrologVariable, PrologTerm> e : argMatcher.entrySet()) {
                        if (matcher.containsKey(e.getKey())) {
                            if (!matcher.get(e.getKey()).equals(e.getValue())) {
                                return null;
                            }
                        } else {
                            matcher.put(e.getKey(), e.getValue());
                        }
                    }
                }
            }
            return matcher;
        } else {
            return null;
        }
    }

    /**
     * @param predications
     * @return
     */
    private List<PrologTerm> createConjunctionListOfPredications(final ArrayList<PrologTerm> predications) {
        if (this.isConjunction()) {
            predications.addAll(this.getArgument(0).createConjunctionListOfPredications());
            return this.getArgument(1).createConjunctionListOfPredications(predications);
        } else {
            // assume we have an atom
            predications.add(this);
            return predications;
        }
    }

    /**
     * @param occ
     * @return
     */
    private List<Occurrence> createListOfPredicationPositions(final Occurrence occ) {
        final List<Occurrence> res = new ArrayList<Occurrence>();
        if (this.isGoalJunctor()) {
            final Occurrence occ1 = occ.appendChildNumber(0);
            final Occurrence occ2 = occ.appendChildNumber(1);
            res.addAll(this.getArgument(0).createListOfPredicationPositions(occ1));
            res.addAll(this.getArgument(1).createListOfPredicationPositions(occ2));
        } else {
            res.add(occ);
        }
        return res;
    }

    /**
     * @param list
     * @return
     */
    private List<PrologTerm> createListOfPredications(final ArrayList<PrologTerm> list) {
        if (this.isGoalJunctor()) {
            list.addAll(this.getArgument(0).createListOfPredications());
            return this.getArgument(1).createListOfPredications(list);
        } else {
            list.add(this);
            return list;
        }
    }

    /**
     * @param t
     * @param varMap
     * @return
     */
    private boolean equalsWithNonAbstractVarNameChanging(
        final PrologTerm t,
        final Map<PrologNonAbstractVariable, PrologNonAbstractVariable> varMap)
    {
        if (t != null) {
            if (t.isNonAbstractVariable() && this.isNonAbstractVariable()) {
                if (varMap.containsKey(t)) {
                    return this.equals(varMap.get(t));
                } else {
                    varMap.put((PrologNonAbstractVariable) t, (PrologNonAbstractVariable) this);
                    return true;
                }
            }
            if (t.getName().equals(this.getName()) && t.getArity() == this.getArity()) {
                boolean res = true;
                final List<PrologTerm> thisArgs = this.getArguments();
                final List<PrologTerm> otherArgs = t.getArguments();
                for (int i = 0; i < thisArgs.size(); i++) {
                    res &= thisArgs.get(i).equalsWithNonAbstractVarNameChanging(otherArgs.get(i), varMap);
                }
                return res;
            }
        }
        return false;
    }

    /**
     * @param sym
     * @param res
     */
    private void getSubtermsWithFunctionSymbol(final FunctionSymbol sym, final List<PrologTerm> res) {
        if (this.hasEqualFunctionSymbol(sym)) {
            res.add(this);
        }
        for (final PrologTerm child : this.getArguments()) {
            child.getSubtermsWithFunctionSymbol(sym, res);
        }
    }

    /**
     * @return
     */
    private PrologTerm reduceTruesInConjunction() {
        if (this.isTrue()) {
            return null;
        } else if (this.isConjunction()) {
            final PrologTerm reduced1 = this.getArgument(0).reduceTruesInConjunction();
            final PrologTerm reduced2 = this.getArgument(1).reduceTruesInConjunction();
            if (reduced1 == null && reduced2 == null) {
                return null;
            } else if (reduced1 == null) {
                return reduced2;
            } else if (reduced2 == null) {
                return reduced1;
            } else {
                return PrologTerms.createConjunction(reduced1, reduced2);
            }
        } else {
            return this;
        }
    }

}
