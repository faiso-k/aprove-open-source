package aprove.verification.dpframework.Utility.NonLoop.structures;

import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import aprove.xml.*;
import immutables.*;

/**
 * A <b>PatternTerm</b> consists of:
 * <ol>
 * <li>{@link TRSTerm} t</li>
 * <li>{@link TRSSubstitution} \sigma</li>
 * <li>{@link TRSSubstitution} \mu</li>
 * </ol>
 *
 * @author Tim Enger
 */

public class PatternTerm implements Exportable, Immutable, XMLObligationExportable, CPFAdditional {

    private final TRSTerm t;
    private final TRSSubstitution sigma;
    private final TRSSubstitution mu;

    private final int hashCode;

    /**
     * Constructor.
     *
     * @param tArg
     *            The {@link TRSTerm} t.
     * @param sigmaArg
     *            The {@link TRSSubstitution} sigma. <tt>Null</tt> will be replaced
     *            by the empty {@link TRSSubstitution}.
     * @param muArg
     *            The {@link TRSSubstitution} mu. <tt>Null</tt> will be replaced by
     *            the empty {@link TRSSubstitution}.
     */
    public PatternTerm(final TRSTerm tArg, final TRSSubstitution sigmaArg, final TRSSubstitution muArg) {
        this.t = tArg;

        if (sigmaArg != null) {
            this.sigma = sigmaArg;
        } else {
            this.sigma = TRSSubstitution.create();
        }
        if (muArg != null) {
            this.mu = muArg;
        } else {
            this.mu = TRSSubstitution.create();
        }

        this.hashCode =
            tArg.getStandardRenumbered().hashCode() * 17 + this.sigma.hashCode() * 23 + this.mu.hashCode() * 27;
    }

    /**
     * Constructor with only the {@link TRSTerm} t as argument. The substitutions
     * sigma and mu will be replaced by the empty substitution.
     *
     * @param tArg
     *            The {@link TRSTerm} t.
     */
    public PatternTerm(final TRSTerm tArg) {
        this(tArg, TRSSubstitution.create(), TRSSubstitution.create());
    }

    /**
     * Constructor with only the {@link TRSTerm} t and the substitution sigma as
     * arguments. Mu will be replaced by the empty substitution.
     *
     * @param tArg
     *            The {@link TRSTerm} t.
     * @param sigmaArg
     *            The {@link TRSSubstitution} sigma.
     */
    public PatternTerm(final TRSTerm tArg, final TRSSubstitution sigmaArg) {
        this(tArg, sigmaArg, TRSSubstitution.create());
    }

    /**
     * @return If sigma and mu are both empty substitutions.
     */
    public boolean isSigmaAndMuEmpty() {
        return this.sigma.isEmpty() && this.mu.isEmpty();
    }

    /**
     * The domain variables of a {@link PatternTerm PatternTerm t = v\sigma\mu}
     * are the variables of the domain of \sigma and \mu, i.e.<br>
     * <br>
     * dv(t) := dom(\sigma) \cup \dom(\mu)
     *
     * @return The {@link Set} of domain variables of {@link PatternTerm this}.
     */
    public Set<TRSVariable> getDomainVariables() {
        final Set<TRSVariable> vars = new LinkedHashSet<>(this.getSigma().getDomain());
        vars.addAll(this.getMu().getDomain());
        return vars;
    }

    /**
     * @return The {@link Set> of {@link TRSVariable variables} that are variables
     *         of the {@link TRSTerm Term t} but not in the domain variables.
     */
    public Set<TRSVariable> getNonDomainVariables() {
        final Set<TRSVariable> vars = new LinkedHashSet<>(this.getAllVariables());
        vars.removeAll(this.getDomainVariables());
        return vars;
    }

    public TRSSubstitution getDomainRenaming(final Set<TRSVariable> toRename, final Set<TRSVariable> used) {
        return this.getDomainRenaming(toRename, new LinkedHashMap<TRSVariable, TRSTerm>(), used);
    }

    /**
     * <p>
     * A Domain Renaming is a {@link TRSSubstitution Substitution \theta} for which
     * the following holds:
     * <ul>
     * <li>dom(\theta) \subseteq dv(v)</li>
     * <li>range(rho) \cap V(v) = \emptyset</li>
     * </ul>
     * </p>
     *
     * @param toRename
     *            {@link Set} of {@link TRSVariable variables} that should be
     *            renamed. Must be a subset of or equal the domain variables and
     *            must not be <tt>null</tt>.
     * @param mapping
     *            Try to use this mapping from Variables to Term. If the mapping
     *            maps a Variable to a Variable that is forbidden, the method
     *            returns null.<br>
     *            To ease the use of this method with substitutions the Map maps
     *            from Variables to Terms. But it has to be a mapping from
     *            Variables to Variables.
     * @param used
     *            Avoid the {@link TRSVariable variables} of this {@link Set}.
     * @return A new {@link TRSSubstitution domain renaming}. If <tt>toRename</tt>
     *         is not a subset or equal the domain variables, <tt>null</tt> is
     *         returned.
     */
    public TRSSubstitution getDomainRenaming(final Set<TRSVariable> toRename,
        final Map<TRSVariable, ? extends TRSTerm> mapping,
        final Set<TRSVariable> used) {

        // toRename must be a subset of or equal the domain variables
        if (!this.getDomainVariables().containsAll(toRename)) {
            return null;
        }

        final Set<TRSVariable> forbidden = new LinkedHashSet<>(this.getAllVariables());

        if (used != null) {
            forbidden.addAll(used);
        }

        final Set<String> usedNames = new LinkedHashSet<>();

        for (final TRSVariable x : forbidden) {
            usedNames.add(x.getName());
        }
        final FreshNameGenerator gen = new FreshNameGenerator(usedNames, new PrefixNameGenerator("x"));
        // FreshVarGenerator gen = new FreshVarGenerator(forbidden);

        final Map<TRSVariable, TRSVariable> thetaMap = new LinkedHashMap<>();
        final Map<TRSVariable, TRSVariable> thetaMapInv = new LinkedHashMap<>();

        for (final TRSVariable var : toRename) {
            TRSVariable freshVar = (TRSVariable) mapping.get(var);

            if (freshVar != null) {
                // check if we are allowed to name it like the mapping says
                if (forbidden.contains(freshVar)) {
                    return null;
                }
            } else {
                freshVar = TRSTerm.createVariable(gen.getFreshName(var.getName(), false));
                // freshVar = gen.getFreshVariable(var, false);
            }

            thetaMap.put(var, freshVar);
            thetaMapInv.put(freshVar, var);
        }
        return TRSSubstitution.create(ImmutableCreator.create(thetaMap));
    }

    public PatternTerm getDomainRenamed(final TRSSubstitution dr) {

        if (!this.isDomainRenaming(dr)) {
            return null;
        }

        final TRSTerm newT = this.t.applySubstitution(dr);

        final TRSSubstitution newSigma = Utils.applyInDomainAndRange(this.sigma, dr);
        TRSSubstitution newMu = Utils.applyInDomain(this.mu, dr);

        // build dr^-1

        final Map<TRSVariable, TRSVariable> drMapInv = new LinkedHashMap<>();

        for (final TRSVariable var : dr.getDomain()) {
            drMapInv.put((TRSVariable) dr.substitute(var), var);
        }

        newMu = newMu.compose(TRSSubstitution.create(ImmutableCreator.create(drMapInv)));

        return new PatternTerm(newT, newSigma, newMu);
    }

    public boolean isDomainRenaming(final TRSSubstitution theta) {
        if (!theta.isVariableRenaming()) {
            return false;
        }
        final Set<TRSVariable> dv = this.getDomainVariables();
        // dom(theta) \subseteq dv(this)
        if (!dv.containsAll(theta.getDomain())) {
            return false;
        }

        // range(theta) \cap V(this) = \emptyset
        final Set<TRSVariable> range = new LinkedHashSet<>(theta.getVariablesInCodomain());
        range.retainAll(this.getAllVariables());

        if (!range.isEmpty()) {
            return false;
        }

        return true;
    }

    /**
     * <p>
     * Compute the set of relevant {@link TRSVariable variables} <tt>rv(this)</tt>.
     * </p>
     * <p>
     * For a {@link PatternTerm} p = t\sigma^n\mu, the set of relevant variables
     * is defined as the smallest set such that V(t) \subseteg rv(p) and such
     * that V(x\sigma) \subseteq rv(p) holds for all x \in rv(p).
     * </p>
     *
     * @return The set of all relevant {@link TRSVariable variables}.
     */
    public Set<TRSVariable> getRelevantVariables() {
        final List<TRSVariable> toCheck = new ArrayList<>(this.t.getVariables());
        final Set<TRSVariable> checked = new LinkedHashSet<>();

        while (!toCheck.isEmpty()) {
            final TRSVariable x = toCheck.remove(0);
            checked.add(x);

            final Set<TRSVariable> newVars = x.applySubstitution(this.sigma).getVariables();

            for (final TRSVariable var : newVars) {
                final boolean member = checked.contains(var);
                if (!member) {
                    toCheck.add(var);
                }
            }
        }

        return checked;
    }

    /**
     *
     */
    public Set<TRSVariable> getInstanceVariables() {
        final Set<TRSVariable> instVars = new LinkedHashSet<>();

        for (final TRSVariable x : this.getRelevantVariables()) {
            instVars.addAll(x.applySubstitution(this.mu).getVariables());
        }

        return instVars;
    }

    /**
     * Remove the irrelevant pattern substitutions.
     *
     * @return A new {@link PatternTerm} in which all irrelevant pattern
     *         substitutions are removed.
     */
    public PatternTerm removeIrrelevantPatternSubs() {
        final Pair<TRSSubstitution, TRSSubstitution> subs = this.getOnlyRelevantPatternSubs();

        return new PatternTerm(this.getT(), subs.x, subs.y);
    }

    /**
     * Get {@link TRSSubstitution sigma'} and {@link TRSSubstitution mu'} containing
     * only the substitutions of all relevant variables.
     *
     * @return A {@link Pair} of {@link TRSSubstitution substitutions sigma' and
     *         mu'}, each containing only the relevant pattern substitutions.
     */
    public Pair<TRSSubstitution, TRSSubstitution> getOnlyRelevantPatternSubs() {
        final Set<TRSVariable> relVars = new LinkedHashSet<>(this.getRelevantVariables());

        final TRSSubstitution sigmaPrime = this.sigma.restrictTo(relVars);
        final TRSSubstitution muPrime = this.mu.restrictTo(relVars);

        return new Pair<>(sigmaPrime, muPrime);
    }

    public PatternTerm addUnused(final TRSSubstitution sigmaPrime, final TRSSubstitution muPrime) {
        final Set<TRSVariable> doms = new LinkedHashSet<>(sigmaPrime.getDomain());
        doms.addAll(muPrime.getDomain());

        doms.retainAll(this.getRelevantVariables());

        if (!doms.isEmpty()) {
            assert false;
            return null;
        }

        return new PatternTerm(this.t, this.getSigma().compose(sigmaPrime), this.getMu().compose(muPrime));
    }

    public PatternTerm simplifyMu(final TRSSubstitution thetaPrime, final TRSSubstitution theta) {

        if (!this.mu.equals(thetaPrime.compose(theta))) {
            return null;
        }

        if (!Utils.commutative(thetaPrime, this.sigma)) {
            return null;
        }

        return new PatternTerm(this.getT().applySubstitution(thetaPrime), this.getSigma(), theta);
    }

    public PatternTerm substitution(final TRSSubstitution theta) {

        for (final Entry<TRSVariable, ? extends TRSTerm> xy : theta.toMap().entrySet()) {

            final TRSTerm term = xy.getValue();
            if (!term.isVariable()) {
                return null;
            }

            final TRSVariable x = xy.getKey();
            final TRSVariable y = (TRSVariable) xy.getValue();

            // check for equivalence
            PatternTerm xt = new PatternTerm(x, this.sigma, this.mu);
            PatternTerm yt = new PatternTerm(y, this.sigma, this.mu);

            xt = xt.removeIrrelevantPatternSubs();
            yt = yt.removeIrrelevantPatternSubs();

            final Map<TRSVariable, TRSVariable> mapping = new LinkedHashMap<>();
            mapping.put(y, x);

            final TRSSubstitution dr = yt.getDomainRenaming(mapping.keySet(), mapping, null);

            if (dr == null) {
                return null;
            }

            yt = yt.getDomainRenamed(dr);

            if (!xt.equals(yt)) {
                return null;
            }
        }

        PatternTerm result = new PatternTerm(this.getT().applySubstitution(theta), this.sigma, this.mu);
        result = result.removeIrrelevantPatternSubs();

        return result;
    }

    /**
     * Find biggest {@link TRSSubstitution mu'} and corresponding
     * {@link TRSSubstitution mu''} such that<br>
     * t\mu'\sigma\mu'' is equvalent to t\sigma\mu
     *
     * @return result.x = mu' and result.y = mu'', such that t\mu'\sigma\mu'' is
     *         equvalent to t\sigma\mu
     */
    public Pair<TRSSubstitution, TRSSubstitution> findEquivalentMus() {

        final Map<TRSVariable, TRSTerm> muPrimeMap = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> newMuMap = new LinkedHashMap<>();

        final ImmutableSet<TRSVariable> domSigma = this.sigma.getDomain();
        final Set<TRSVariable> dv = this.getDomainVariables();

        for (final TRSVariable x : this.mu.getDomain()) {
            final TRSTerm xSigma = x.applySubstitution(this.sigma);
            final TRSTerm xMu = x.applySubstitution(this.mu);

            if (domSigma.contains(x)) {
                final TRSSubstitution theta = xSigma.getMatcher(xMu);

                if (theta != null) {
                    muPrimeMap.put(x, xSigma);
                    newMuMap.put(x, x.applySubstitution(theta));
                } else {
                    // just leave it
                    newMuMap.put(x, xMu);
                }
            } else {
                final Set<TRSVariable> intersect = xMu.getVariables();
                intersect.retainAll(dv);
                // x/xMu commutes with sigma
                final TRSSubstitution xxMu = TRSSubstitution.create(x, xMu);
                if (intersect.isEmpty() && Utils.commutative(xxMu, this.sigma)) {
                    muPrimeMap.put(x, xMu);
                } else {
                    // just leave it
                    newMuMap.put(x, xMu);
                }
            }
        }

        TRSSubstitution muPrime = TRSSubstitution.create(ImmutableCreator.create(muPrimeMap));
        TRSSubstitution newMu = TRSSubstitution.create(ImmutableCreator.create(newMuMap));

        if (!muPrime.compose(newMu).equals(this.mu)) {
            // keep the old mu
            newMu = this.mu;
            muPrime = TRSSubstitution.EMPTY_SUBSTITUTION;
        }

        return new Pair<TRSSubstitution, TRSSubstitution>(muPrime, newMu);
    }

    /**
     * @return The {@link TRSTerm} t.
     */
    public TRSTerm getT() {
        return this.t;
    }

    /**
     * @return The sigma-{@link TRSSubstitution}.
     */
    public TRSSubstitution getSigma() {
        return this.sigma;
    }

    /**
     * @return The mu-{@link TRSSubstitution}.
     */
    public TRSSubstitution getMu() {
        return this.mu;
    }

    public TRSTerm getInstance(final int n) {
        TRSTerm term = this.t;

        for (int i = 0; i < n; i++) {
            term = term.applySubstitution(this.sigma);
        }

        term = term.applySubstitution(this.mu);

        return term;
    }

    /**
     * Definition 3.3<br>
     * Applying a substitution means:<br>
     * t\sigma^n\mu \delta := t\sigma^n\mu'<br>
     * where \mu' = \sigma\delta
     *
     * @param delta
     *            The substitution to apply
     */
    public PatternTerm applySubstitution(final TRSSubstitution delta) {
        final TRSSubstitution muNew = this.mu.compose(delta);
        return new PatternTerm(this.t, this.sigma, muNew);
    }

    /**
     * @return A {@link Set} of all used {@link TRSVariable Variables} in t, sigma
     *         and mu.
     */
    public Set<TRSVariable> getAllVariables() {
        final Set<TRSVariable> vars = new HashSet<TRSVariable>();

        vars.addAll(this.t.getVariables());
        vars.addAll(this.sigma.getVariables());
        vars.addAll(this.mu.getVariables());

        return vars;
    }

    /**
     * This method returns the subterm of the {@link TRSTerm} t of this
     * {@link PatternTerm} at position <tt>pos</tt>.<br>
     * The caller has to ensure that <code>pos</code> is a valid position of
     * this term.
     *
     * @param pos
     *            The position.
     * @return The {@link TRSTerm Subterm} at {@link Position} pos.
     */
    public TRSTerm getSubterm(final Position pos) {
        return this.t.getSubterm(pos);
    }

    /**
     * @return The non-variable positions, which means the non-variable
     *         positions of t.
     */
    public Set<Position> getNonVarPos() {
        return Utils.getNonVarPos(this.t);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util eu) {
        return this.t.export(eu) + this.sigma.export(eu) + eu.sup("n") + this.mu.export(eu);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(final Object o) {
        if (this == o) {
            return true;
        }
        if (o instanceof PatternTerm) {
            final PatternTerm other = (PatternTerm) o;

            if (this.hashCode == other.hashCode() && this.getT().equals(other.getT()) && this.getSigma().equals(other.getSigma())
                && this.getMu().equals(other.getMu())) {
                return true;
            }
        }
        return false;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternTerm = XMLTag.PATTERN_TERM.createElement(doc);
        patternTerm.appendChild(this.mu.toDOM(doc, xmlMetaData));
        patternTerm.appendChild(this.sigma.toDOM(doc, xmlMetaData));
        patternTerm.appendChild(this.t.toDOM(doc, xmlMetaData));
        return patternTerm;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternTerm = CPFTag.PATTERN_TERM.createElement(doc);
        patternTerm.appendChild(this.t.toCPF(doc, xmlMetaData));
        patternTerm.appendChild(this.mu.toCPF(doc, xmlMetaData));
        patternTerm.appendChild(this.sigma.toCPF(doc, xmlMetaData));
        return patternTerm;
    }

}
