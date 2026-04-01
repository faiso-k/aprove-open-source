package aprove.verification.oldframework.IntTRS.Ranking;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A transition relation consists of a PCS, two function symbols with variables:
 * start and end. Furthermore I assume that occurring variable-sets are always
 * disjoint.
 * @author Matthias Hoelzel
 */
public class TransitionRelation implements Exportable {
    /** The constraints */
    private final PCS pcs;

    /** Where do we start? */
    private final FunctionSymbol startSymbol;

    /** Where do we go? */
    private final FunctionSymbol endSymbol;

    /** What are the start variables? */
    private final List<TRSVariable> startVariables;

    /** What are the end variables? */
    private final List<TRSVariable> endVariables;

    /** How did we create this relation? */
    private final List<TransitionRelation> originRelations;

    /** Stores the hash code to avoid recalculation */
    private Integer hashCodeCache;

    /** Some aborter */
    protected final Abortion aborter;

    /**
     * Constructor! Amazing!
     * @param constraints the transition constraints
     * @param startSym the start symbol
     * @param startVars the start variables, disjoint from endVars
     * @param endSym the end symbol
     * @param endVars the end variables, disjoint from startVars
     * @param eliminateFreeVariables true if you want to eliminate free variables
     * @param abortion some aborter
     * @throws AbortionException can be aborted
     */
    public TransitionRelation(
        final PCS constraints,
        final FunctionSymbol startSym,
        final List<TRSVariable> startVars,
        final FunctionSymbol endSym,
        final List<TRSVariable> endVars,
        final boolean eliminateFreeVariables,
        final Abortion abortion) throws AbortionException
    {
        this(
            constraints,
            startSym,
            startVars,
            endSym,
            endVars,
            new LinkedList<TransitionRelation>(),
            eliminateFreeVariables,
            abortion);
    }

    /**
     * Constructor!
     * @param constraints the transition constraints
     * @param startSym the start symbol
     * @param startVars the start variables, disjoint from endVars
     * @param endSym the end symbol
     * @param endVars the end variables, disjoint from startVars
     * @param origin list of transition relations from which this was created
     * @param eliminateFreeVariables true if you want to eliminate free
     * variables
     * @param abortion some aborter
     * @throws AbortionException can be aborted
     */
    public TransitionRelation(
        final PCS constraints,
        final FunctionSymbol startSym,
        final List<TRSVariable> startVars,
        final FunctionSymbol endSym,
        final List<TRSVariable> endVars,
        final List<TransitionRelation> origin,
        final boolean eliminateFreeVariables,
        final Abortion abortion) throws AbortionException
    {
        this.startSymbol = startSym;
        this.endSymbol = endSym;
        this.startVariables = startVars;
        this.endVariables = endVars;
        this.aborter = abortion;
        if (eliminateFreeVariables && constraints.isLinear()) {
            final LinkedHashSet<String> allowedVariables =
                new LinkedHashSet<>(this.startVariables.size() + this.endVariables.size());
            for (final TRSVariable v : this.startVariables) {
                allowedVariables.add(v.getName());
            }
            for (final TRSVariable v : this.endVariables) {
                allowedVariables.add(v.getName());
            }
            this.pcs = constraints.eliminateOtherVariables(allowedVariables).cleanUp();
        } else {
            this.pcs = constraints.cleanUp();
        }
        this.originRelations = origin;

        if (this.pcs == null
            || this.startSymbol == null
            || this.endSymbol == null
            || endVars == null
            || this.endVariables == null)
        {
            throw new UnsupportedOperationException("Can't create ranking, because parameter is null!");
        }
        if (this.startSymbol.getArity() != this.startVariables.size()
            || this.endSymbol.getArity() != this.endVariables.size())
        {
            throw new UnsupportedOperationException("Symbols and variables don't fit together!");
        }
        if (Globals.DEBUG_MATTHIAS) {
            for (final TRSVariable v : this.startVariables) {
                assert !this.endVariables.contains(v) : "Start and end vars not disjoint!";
            }
            for (final TRSVariable v : this.endVariables) {
                assert !this.startVariables.contains(v) : "Start and end vars not disjoint!";
            }
        }
    }

    /**
     * Returns true, if we know that this relation is well-founded. Please note,
     * that it may return a false negative answer.
     * @return boolean
     */
    public boolean isCertainlyWellFounded() {
        return !this.startSymbol.equals(this.endSymbol);
    }

    /**
     * Returns true, if we know that this relation is contained in another
     * relation. May return a false negative answer. (Please note: that this
     * method will be overwritten!)
     * @param other the other transition relation
     * @return boolean
     * @throws AbortionException can be aborted
     */
    public boolean containsRelation(final TransitionRelation other) throws AbortionException {
        return false;
    }

    /**
     * We say, that relations R_1 and R_2 might form a chain, iff the end symbol
     * of R_1 equals the start symbol of R_2.
     * @param other the other relation
     * @return boolean
     */
    public boolean mightFormChainWith(final TransitionRelation other) {
        assert other != null : "other should not be null";

        return this.endSymbol.equals(other.startSymbol);
    }

    /**
     * Return a renamed version of this where we use the same names for the
     * start and end variables, that the other relation does. This is useful for
     * comparing relation using the same symbols.
     * @param other TransitionRelation
     * @param aborter some aborter
     * @return TransitionRelation
     * @throws AbortionException can be aborted
     */
    public TransitionRelation renameStartAndEndVariables(final TransitionRelation other, final Abortion aborter)
        throws AbortionException
    {
        if (other == null || !this.startSymbol.equals(other.startSymbol) || !this.endSymbol.equals(other.endSymbol)) {
            assert false : "Invalid transition relation!";
            return null;
        }
        final LinkedHashMap<String, VarPolynomial> renaming =
            new LinkedHashMap<>(this.startSymbol.getArity() + this.endSymbol.getArity());

        final Iterator<TRSVariable> startVarIterator = this.startVariables.iterator();
        final Iterator<TRSVariable> newStartVarIterator = other.startVariables.iterator();
        while (startVarIterator.hasNext()) {
            final TRSVariable thisVar = startVarIterator.next();
            final TRSVariable otherVar = newStartVarIterator.next();
            renaming.put(thisVar.getName(), VarPolynomial.createVariable(otherVar.getName()));
        }

        final Iterator<TRSVariable> endVarIterator = this.endVariables.iterator();
        final Iterator<TRSVariable> newEndVarIterator = other.endVariables.iterator();
        while (endVarIterator.hasNext()) {
            final TRSVariable thisVar = endVarIterator.next();
            final TRSVariable otherVar = newEndVarIterator.next();
            renaming.put(thisVar.getName(), VarPolynomial.createVariable(otherVar.getName()));
        }

        final List<GEConstraint> newGEConstraints = new LinkedList<>();
        for (final GEConstraint constraint : this.pcs.getConstraints()) {
            final GEConstraint newConstraint = constraint.substitute(renaming, aborter);
            newGEConstraints.add(newConstraint);
        }

        return new TransitionRelation(
            new PCS(newGEConstraints, this.aborter),
            this.startSymbol,
            other.startVariables,
            this.endSymbol,
            other.endVariables,
            false,
            this.aborter);
    }

    /**
     * Returns a renamed version of this.
     * @param ng a name generator
     * @param aborter some aborter
     * @return TransitionRelation
     * @throws AbortionException can be aborted
     */
    public TransitionRelation rename(final FreshNameGenerator ng, final Abortion aborter) throws AbortionException {
        final LinkedHashMap<String, VarPolynomial> renaming = new LinkedHashMap<>();

        final LinkedList<TRSVariable> newStartVariables = new LinkedList<>();
        final LinkedList<TRSVariable> newEndVariables = new LinkedList<>();

        final Iterator<TRSVariable> startVariableIterator = this.startVariables.iterator();
        while (startVariableIterator.hasNext()) {
            final TRSVariable current = startVariableIterator.next();
            final String newName = ng.getFreshName(RankingUtil.LEFT_VARIABLE_NAME, false);

            renaming.put(current.getName(), VarPolynomial.createVariable(newName));
            newStartVariables.add(TRSTerm.createVariable(newName));
        }

        final Iterator<TRSVariable> endVariableIterator = this.endVariables.iterator();
        while (endVariableIterator.hasNext()) {
            final TRSVariable current = endVariableIterator.next();
            final String newName = ng.getFreshName(RankingUtil.RIGHT_VARIABLE_NAME, false);

            renaming.put(current.getName(), VarPolynomial.createVariable(newName));
            newEndVariables.add(TRSTerm.createVariable(newName));
        }

        for (final GEConstraint constraint : this.pcs.getConstraints()) {
            for (final String var : constraint.getPoly().getVariables()) {
                if (!renaming.containsKey(var)) {
                    final String newName = ng.getFreshName(RankingUtil.FREE_VARIABLE_NAME, false);
                    renaming.put(var, VarPolynomial.createVariable(newName));
                }
            }
        }

        final List<GEConstraint> newConstraints = new LinkedList<>();
        for (final GEConstraint constraint : this.pcs.getConstraints()) {
            newConstraints.add(constraint.substitute(renaming, aborter));
        }
        final PCS newPCS = new PCS(newConstraints, this.aborter);

        return new TransitionRelation(
            newPCS,
            this.startSymbol,
            newStartVariables,
            this.endSymbol,
            newEndVariables,
            this.originRelations,
            false,
            this.aborter);
    }

    /**
     * Construct the concatenation of this and the other relation. Should only
     * be called, if mightFormChainWith returned true.
     * @param other TransitionRelation
     * @param ng name generator
     * @return TransitionRelation
     * @throws AbortionException can be aborted
     */
    public
        TransitionRelation
        concat(final TransitionRelation other, final FreshNameGenerator ng, final Abortion aborter)
            throws AbortionException
    {
        if (!this.mightFormChainWith(other)) {
            throw new UnsupportedOperationException("I don't like empty relations!");
        }
        final TransitionRelation otherRenamed = other.rename(ng, aborter);

        // Initialize some data-structures:
        final LinkedList<TRSVariable> newStartVariables = new LinkedList<>();
        final LinkedList<TRSVariable> newEndVariables = new LinkedList<>();

        final int numberOfFreeVariables = this.endSymbol.getArity();
        final LinkedHashMap<String, VarPolynomial> leftSubstitution =
            new LinkedHashMap<>(numberOfFreeVariables + this.startSymbol.getArity());
        final LinkedHashMap<String, VarPolynomial> rightSubstitution =
            new LinkedHashMap<>(numberOfFreeVariables + this.startSymbol.getArity());

        // Generate new names for the new start and end variables:
        for (final TRSVariable oldStartVar : this.startVariables) {
            final String newName = ng.getFreshName("x", false);
            newStartVariables.add(TRSTerm.createVariable(newName));
            leftSubstitution.put(oldStartVar.getName(), VarPolynomial.createVariable(newName));
        }
        for (final TRSVariable oldEndVar : otherRenamed.endVariables) {
            final String newName = ng.getFreshName("z", false);
            newEndVariables.add(TRSTerm.createVariable(newName));
            rightSubstitution.put(oldEndVar.getName(), VarPolynomial.createVariable(newName));
        }

        // Generate new names for the free variables:
        final Iterator<TRSVariable> leftEndVarIterator = this.endVariables.iterator();
        final Iterator<TRSVariable> rightStartVarIterator = otherRenamed.startVariables.iterator();
        for (int i = 0; i < numberOfFreeVariables; i++) {
            final String newName = ng.getFreshName("y", false);
            leftSubstitution.put(leftEndVarIterator.next().getName(), VarPolynomial.createVariable(newName));
            rightSubstitution.put(rightStartVarIterator.next().getName(), VarPolynomial.createVariable(newName));
        }

        // Generate the new constraint:
        final LinkedList<GEConstraint> newConstraints = new LinkedList<>();
        for (final GEConstraint leftConstraint : this.pcs.getConstraints()) {
            final GEConstraint newLeftConstraint = leftConstraint.substitute(leftSubstitution, aborter);
            newConstraints.add(newLeftConstraint);
        }
        for (final GEConstraint rightConstraint : otherRenamed.pcs.getConstraints()) {
            final GEConstraint newRightConstraint = rightConstraint.substitute(rightSubstitution, aborter);
            newConstraints.add(newRightConstraint);
        }

        // Put everything together and return the new relation:
        final PCS newPCS = new PCS(newConstraints, this.aborter);

        final List<TransitionRelation> originList = new LinkedList<>();
        originList.add(this);
        originList.add(other);

        final TransitionRelation result =
            new TransitionRelation(
                newPCS,
                this.startSymbol,
                newStartVariables,
                otherRenamed.endSymbol,
                newEndVariables,
                originList,
                true,
                this.aborter);

        return result;
    }

    /**
     * Getter for pcs.
     * @return PCS
     */
    public PCS getPCS() {
        return this.pcs;
    }

    /**
     * Getter for the start symbol.
     * @return FunctionSymbol
     */
    public FunctionSymbol getStartSymbol() {
        return this.startSymbol;
    }

    /**
     * Getter for the end symbol.
     * @return FunctionSymbol
     */
    public FunctionSymbol getEndSymbol() {
        return this.endSymbol;
    }

    /**
     * Getter for the start variables.
     * @return List of variables
     */
    public List<TRSVariable> getStartVariables() {
        return this.startVariables;
    }

    /**
     * Getter for the end variables.
     * @return List of variables
     */
    public List<TRSVariable> getEndVariables() {
        return this.endVariables;
    }

    /**
     * Getter for the origin relations.
     * @return list of relation, used to create this relation.
     */
    public List<TransitionRelation> getOriginRelations() {
        return this.originRelations;
    }

    /**
     * Returns a set of monomials, which only use end variables.
     * @return set of IndefiniteParts
     */
    public Set<IndefinitePart> getRightMonomials() {
        final LinkedHashSet<IndefinitePart> result = new LinkedHashSet<>();
        this.collectMonomials(this.endVariables, result);
        return result;
    }

    /**
     * Returns a set of monomials, which only use start variables.
     * @return set of IndefiniteParts
     */
    public Set<IndefinitePart> getLeftMonomials() {
        final LinkedHashSet<IndefinitePart> result = new LinkedHashSet<>();
        this.collectMonomials(this.startVariables, result);
        return result;
    }

    /**
     * Collects monomials, which only use the specified variables. Called by
     * getLeftMonomials & getRightMonomials.
     * @param allowedVariables the set of allowed variables
     * @param resultSet set to be completed
     */
    private void collectMonomials(
        final Collection<TRSVariable> allowedVariables,
        final LinkedHashSet<IndefinitePart> resultSet)
    {
        for (final GEConstraint constraint : this.pcs.getConstraints()) {
            final VarPolynomial poly = constraint.getPoly();
            for (final IndefinitePart indefPart : poly.getVarMonomials().keySet()) {
                // Take only those monomials, consisting of allowed variables:
                boolean allowed = true;

                for (final String varName : indefPart.getIndefinites()) {
                    if (!allowedVariables.contains(TRSTerm.createVariable(varName))) {
                        allowed = false;
                        break;
                    }
                }

                if (allowed) {
                    resultSet.add(indefPart);
                }
            }
        }
    }

    /**
     * Concatenates the rules from the origin to create a less intricate
     * relation.
     * @param ng generates some new names
     * @param aborter some aborter
     * @return TransitionRelation
     * @throws AbortionException can be aborted
     */
    public TransitionRelation concatHistory(final FreshNameGenerator ng, final Abortion aborter)
        throws AbortionException
    {
        if (this.originRelations.isEmpty()) {
            return this;
        } else {
            final Iterator<TransitionRelation> tri = this.originRelations.iterator();
            TransitionRelation result = tri.next().concatHistory(ng, aborter);
            while (tri.hasNext()) {
                result = result.concat(tri.next().concatHistory(ng, aborter), ng, aborter);
            }
            return result;
        }
    }

    /**
     * Adds all monotonicity constraints, which speak about the start and end
     * variables.
     * @return PCS
     */
    public PCS getMonotonicitySystem() {
        final LinkedHashSet<String> startAndEndVariables =
            new LinkedHashSet<>(this.startVariables.size() + this.endVariables.size());
        for (final TRSVariable v : this.startVariables) {
            startAndEndVariables.add(v.getName());
        }
        for (final TRSVariable v : this.endVariables) {
            startAndEndVariables.add(v.getName());
        }

        final LinkedList<GEConstraint> resultConstraints = new LinkedList<>();
        for (final GEConstraint c : this.pcs.getConstraints()) {
            final Set<String> occVars = c.getVariables();
            if (startAndEndVariables.containsAll(occVars) && c.getConstant().compareTo(BigInteger.ZERO) >= 0) {
                resultConstraints.add(GEConstraint.create(c.getPoly(), BigInteger.ZERO));
            }
        }
        return new PCS(resultConstraints, this.aborter);
    }

    @Override
    public int hashCode() {
        if (this.hashCodeCache == null) {
            this.hashCodeCache =
                17
                    * this.endSymbol.hashCode()
                    + 23
                    * this.startSymbol.hashCode()
                    + 31
                    * this.endVariables.hashCode()
                    + 47
                    * this.startVariables.hashCode()
                    + 97
                    * this.pcs.hashCode();
        }
        return this.hashCodeCache;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final TransitionRelation other = (TransitionRelation) obj;
        if (this.endSymbol == null) {
            if (other.endSymbol != null) {
                return false;
            }
        } else if (!this.endSymbol.equals(other.endSymbol)) {
            return false;
        }
        if (this.endVariables == null) {
            if (other.endVariables != null) {
                return false;
            }
        } else if (!this.endVariables.equals(other.endVariables)) {
            return false;
        }
        if (this.pcs == null) {
            if (other.pcs != null) {
                return false;
            }
        } else if (!this.pcs.equals(other.pcs)) {
            return false;
        }
        if (this.startSymbol == null) {
            if (other.startSymbol != null) {
                return false;
            }
        } else if (!this.startSymbol.equals(other.startSymbol)) {
            return false;
        }
        if (this.startVariables == null) {
            if (other.startVariables != null) {
                return false;
            }
        } else if (!this.startVariables.equals(other.startVariables)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append(this.startSymbol);
        sb.append(this.startVariables);
        sb.append(" -> ");
        sb.append(this.endSymbol);
        sb.append(this.endVariables);

        if (!this.pcs.getConstraints().isEmpty()) {
            sb.append(" | ");
            for (final GEConstraint constraint : this.pcs.getConstraints()) {
                sb.append("\n\t");
                sb.append(constraint);
            }
        }
        sb.append('\n');
        return sb.toString();
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        sb.append(this.startSymbol.export(eu));
        sb.append(eu.escape("("));
        final Iterator<TRSVariable> startIter = this.startVariables.iterator();
        while (startIter.hasNext()) {
            sb.append(startIter.next().export(eu));
            if (startIter.hasNext()) {
                sb.append(eu.escape(", "));
            }
        }
        sb.append(eu.escape(")"));
        sb.append(eu.rightarrow());
        sb.append(this.endSymbol.export(eu));
        sb.append(eu.escape("("));
        final Iterator<TRSVariable> endIter = this.endVariables.iterator();
        while (endIter.hasNext()) {
            sb.append(endIter.next().export(eu));
            if (endIter.hasNext()) {
                sb.append(eu.escape(", "));
            }
        }
        sb.append(eu.escape(") "));
        sb.append(eu.pipeSign());
        sb.append(eu.linebreak());
        sb.append(this.pcs.export(eu));

        return sb.toString();
    }
}
