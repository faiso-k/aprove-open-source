package aprove.verification.dpframework.Utility.NonLoop;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class Utils {

    /**
     * Find two {@link TRSSubstitution substitutions \theta, \sigma} such that<br>
     * {@link TRSTerm l\sigma} = {@link TRSTerm r\theta}.
     *
     * @param l
     *        {@link TRSTerm}
     * @param r
     *        {@link TRSTerm}
     * @return A {@link Pair} of {@link TRSSubstitution substitutions} where
     *         {@link TRSSubstitution pair.x} is \sigma and {@link TRSSubstitution
     *         pair.y} is \theta. <tt>Null</tt> if such {@link TRSSubstitution
     *         substitutions} could not be found.
     */
    public static Pair<TRSSubstitution, TRSSubstitution> findSubstitutions(final TRSTerm l,
        final TRSTerm r) {
        Pair<TRSSubstitution, TRSSubstitution> result = null;

        // renaming phi of l to l' such that Var(l') and Var(r) = \emptyset
        final FreshVarGenerator gen = new FreshVarGenerator(r.getVariables());
        final Map<TRSVariable, TRSVariable> phi = new LinkedHashMap<TRSVariable, TRSVariable>();
        final Map<TRSVariable, TRSVariable> phiInv =
            new LinkedHashMap<TRSVariable, TRSVariable>();

        Utils.getRenaming(l.getVariables(), gen, phi, phiInv);

        final TRSTerm lnew =
            l.applySubstitution(TRSSubstitution.create(ImmutableCreator.create(phi)));

        final TRSSubstitution sigma = lnew.getMGU(r);

        if (sigma != null) {
            final TRSSubstitution sigmaL = Utils.buildSigmaL(phiInv, lnew, sigma);
            final TRSSubstitution sigmaR = Utils.buildSigmaR(r, phiInv, sigma);

            result = new Pair<>(sigmaL, sigmaR);
        }

        return result;
    }

    /**
     * \sigma_l = { x phi^-1 / t\phi^-1 | x/t \in \sigma, x \in Var(lnew) }
     *
     * @param phiInv
     * @param lnew
     * @param sigma
     * @return The new {@link TRSSubstitution} \sigma_l.
     */
    private static TRSSubstitution buildSigmaL(final Map<TRSVariable, TRSVariable> phiInv,
        final TRSTerm lnew,
        final TRSSubstitution sigma) {

        final Map<TRSVariable, TRSTerm> sigmaLMap = new LinkedHashMap<TRSVariable, TRSTerm>();
        final Map<TRSVariable, ? extends TRSTerm> sigmaMap = sigma.toMap();

        for (final TRSVariable x : lnew.getVariables()) {
            final TRSTerm t = sigmaMap.get(x);
            if (t != null) { // x/t \in \sigma
                TRSTerm newT = t;
                for (final TRSVariable var : phiInv.keySet()) {
                    newT = newT.replaceAll(var, phiInv.get(var));
                }
                sigmaLMap.put(phiInv.get(x), newT); // add new sub
            }
        }

        // build new substitution
        return TRSSubstitution.create(ImmutableCreator.create(sigmaLMap));
    }

    /**
     * \sigma_r = { x / t\phi^-1 | x/t \in \sigma, x \in Var(r) }
     *
     * @param r
     * @param phiInv
     * @param sigma
     * @return The new {@link TRSSubstitution} sigma_r.
     */
    private static TRSSubstitution buildSigmaR(final TRSTerm r,
        final Map<TRSVariable, TRSVariable> phiInv,
        final TRSSubstitution sigma) {

        final Map<TRSVariable, TRSTerm> sigmaRMap = new LinkedHashMap<TRSVariable, TRSTerm>();
        final Map<TRSVariable, ? extends TRSTerm> sigmaMap = sigma.toMap();

        for (final TRSVariable x : r.getVariables()) {
            final TRSTerm t = sigmaMap.get(x);
            if (t != null) { // x/t \in \sigma
                TRSTerm newT = t;
                for (final TRSVariable var : phiInv.keySet()) {
                    newT = newT.replaceAll(var, phiInv.get(var));
                }
                sigmaRMap.put(x, newT); // add new sub
            }
        }

        // build new substitution
        return TRSSubstitution.create(ImmutableCreator.create(sigmaRMap));
    }

    /**
     * <p>
     * Lemma 2.8 (p.
     * </p>
     * <p>
     * Two substitutions sigma and theta are commutative if the following
     * constraints are fulfilled:
     * <ol>
     * <li>\forall x \in dom(\sigma) \cap \dom(theta) : x\sigma = x\theta</li>
     * <li>vran(\sigma) \cap \dom(theta) = \emptyset</li>
     * <li>vran(\theta) \cap \dom(\sigma) = \emptyset</li>
     * </ol>
     * </p>
     *
     * @param sigma
     * @param theta
     * @return <tt>True</tt> if the substitutions are commutative, otherwise
     *         <tt>False</tt>.
     */
    public static boolean commutative(final TRSSubstitution sigma,
        final TRSSubstitution theta) {

        //        ImmutableSet<Variable> domSigma = sigma.getDomain();
        //        ImmutableSet<Variable> domTheta = theta.getDomain();
        //
        //        ImmutableSet<Variable> vranSigma = sigma.getVariablesInCodomain();
        //        ImmutableSet<Variable> vranTheta = theta.getVariablesInCodomain();
        //
        //        /* CONDITION 1 */
        //        Set<Term> intersect = new HashSet<Term>(domSigma);
        //        intersect.retainAll(domTheta);
        //        for (Term x : intersect) {
        //            if (x.applySubstitution(sigma) != x.applySubstitution(theta)) {
        //                return false;
        //            }
        //        }
        //
        //        /* CONDITION 2 */
        //        intersect = new HashSet<Term>(vranSigma);
        //        intersect.retainAll(domTheta);
        //        if (!intersect.isEmpty()) {
        //            return false;
        //        }
        //
        //        /* CONDITION 3 */
        //        intersect = new HashSet<Term>(vranTheta);
        //        intersect.retainAll(domSigma);
        //        if (!intersect.isEmpty()) {
        //            return false;
        //        }

        // try the following
        // forall x \in dom(\sigma) \cup dom(\theta) :
        // x\sigma\theta = x\theta\sigma

        if (sigma.isEmpty() || theta.isEmpty()) {
            return true;
        }

        final List<TRSVariable> union =
            new ArrayList<TRSVariable>(
                sigma.getDomain());
        union.addAll(theta.getDomain());

        for (final TRSVariable x : union) {
            final TRSTerm l =
                x.applySubstitution(sigma).applySubstitution(
                    theta);
            final TRSTerm r =
                x.applySubstitution(theta).applySubstitution(
                    sigma);

            if (!l.equals(r)) {
                return false;
            }
        }

        return true;
    }

    /**
     * <p>
     * Definition 4.11 & 4.15
     * </p>
     * <p>
     * This method creates a {@link TRSSubstitution} \eta' defined as:<br>
     * \eta' := \eta where every c_x \in ran(\phi), occuring in a term in the
     * range of \eta, is replaced by the corresponding x.<br>
     * This means for instance, if x/c_x is in \phi and z/f(c_x) in \eta, z/f(x)
     * would be in \etaStr.<br>
     * In order to make things easier, a map of the constants c_x to the
     * corresponding variables is passed as the parameter<tt>phiMapInv</tt>.
     * </p>
     *
     * @param eta
     *        The {@link TRSSubstitution} \eta.
     * @param phiMapInv
     *        The {@link Map} from constants to variables.
     * @return The new {@link TRSSubstitution} \eta'.
     */
    public static TRSSubstitution replaceConstants(final TRSSubstitution eta,
        final Map<TRSTerm, TRSTerm> phiMapInv) {
        /** build eta' **/
        // this means to replace all former (by constants c_x) replaced
        // variables back to the original variables again.
        final Map<TRSVariable, TRSTerm> etaStrMap = new HashMap<TRSVariable, TRSTerm>();

        for (final TRSVariable var : eta.getDomain()) {
            final TRSTerm repl = eta.substitute(var);
            // every (former introduced) constant in the range of eta is
            // replaced
            // by the corresponding variable
            etaStrMap.put(var, repl.replaceAll(phiMapInv));
        }
        return TRSSubstitution.create(ImmutableCreator.create(etaStrMap));
    }

    /**
     * <p>
     * Definition 4.11 & 4.15
     * </p>
     * <p>
     * The method generates a {@link TRSSubstitution} phi such that<br>
     * <b>\phi :) { x/c_x | x \in dom(\sigma), c_x fresh}</b><br>
     * whereby c_x fresh means w.r.t. functionsymbols and variables used in
     * <tt>t</tt> and <tt>l</tt>.
     * </p>
     *
     * @param t
     *        {@link TRSTerm} t is used to garantuee that generated the constants
     *        are fresh
     * @param l
     *        {@link TRSTerm} l is used to garantuee that generated the constants
     *        are fresh
     * @param patternVars
     *        The {@link Set> of {@link TRSVariable variables} that should be
     *        replaced by constants in phi.
     * @param phiMapInv
     *        Every substitution x/t in phi is saved as (t,x) in this map.
     * @return the new {@link TRSSubstitution} phi.
     */
    public static TRSSubstitution replaceVariables(final TRSTerm t,
        final TRSTerm l,
        final Set<TRSVariable> patternVars,
        final Map<TRSTerm, TRSTerm> phiMapInv) {

        final Map<TRSVariable, TRSTerm> phiMap = new HashMap<TRSVariable, TRSTerm>();

        // create a FreshNameGen based on every symbol in t
        final Set<String> used = new HashSet<String>();
        for (final TRSTerm temp : t) {
            used.add(temp.getName());
        }
        for (final TRSTerm temp : l) {
            used.add(temp.getName());
        }

        final FreshNameGenerator gen =
            new FreshNameGenerator(used, FreshNameGenerator.TYPE_CONS);

        // replace variables of dom(\sigma_t) by new constants
        for (final TRSVariable x : patternVars) {
            final String name = gen.getFreshName(x.getName(), false);
            final TRSFunctionApplication con =
                TRSTerm.createFunctionApplication(
                    FunctionSymbol.create(name, 0), new ArrayList<TRSTerm>());
            phiMap.put(x, con);
            phiMapInv.put(con, x);
        }

        return TRSSubstitution.create(ImmutableCreator.create(phiMap));
    }

    /**
     * This method produces a renaming of the {@link TRSVariable variables}
     * <tt>vars</tt> to new {@link TRSVariable variables}. It puts the mapping from
     * {@link TRSVariable variables} to new {@link TRSVariable variables} to
     * <tt>phi</tt> and the inverse mapping from new {@link TRSVariable variables}
     * to the original {@link TRSVariable variables} to <tt>phiInv</tt>.<br>
     * New variables are generated by the {@link FreshVarGenerator} <tt>gen</tt>
     * .<br>
     * In case of a passed <tt>null</tt> as parameter, the algorithm does
     * nothing.
     *
     * @param vars
     *        The set of variables.
     * @param gen
     *        The FreshNameGenerator
     * @param phi
     *        The map of the old {@link TRSVariable Variables} to the new ones.
     * @param phiInv
     *        The map of the new {@link TRSVariable Variable} mapped on the old
     *        ones.
     * @return A map that maps every variable of <tt>vars</tt> to a new one.
     */
    public static void getRenaming(final Set<TRSVariable> vars,
        final FreshVarGenerator gen,
        final Map<TRSVariable, TRSVariable> phi,
        final Map<TRSVariable, TRSVariable> phiInv) {

        if (phi != null && phiInv != null && vars != null && gen != null) {
            for (final TRSVariable var : vars) {
                if (!phi.containsKey(var)) {
                    final TRSVariable newVar = gen.getFreshVariable(var, true);
                    phi.put(var, newVar);
                    phiInv.put(newVar, var);
                }
            }
        }
    }

    /**
     * Get the non-variable positions of a {@link TRSTerm}.
     *
     * @param t
     *        The {@link TRSTerm}.
     * @return The {@link Set} of non-variable positions in <tt>t</tt>.
     */
    public static Set<Position> getNonVarPos(final TRSTerm t) {
        // non-variable position of r
        final Set<Position> pos = t.getPositions();
        for (final List<Position> varPos : t.getVariablePositions().values()) {
            pos.removeAll(varPos);
        }
        return pos;
    }

    /**
     * @param sigma
     * @param theta
     * @return {x\theta/t\theta | x/t \in \sigma}
     */

    public static TRSSubstitution applyInDomainAndRange(final TRSSubstitution sigma,
        final TRSSubstitution theta) {
        final Map<TRSVariable, TRSTerm> newSigmaMap = new LinkedHashMap<>();

        for (final Entry<TRSVariable, ? extends TRSTerm> entry : sigma.toMap().entrySet()) {
            final TRSVariable key = (TRSVariable) entry.getKey().applySubstitution(theta);
            final TRSTerm value = entry.getValue().applySubstitution(theta);
            newSigmaMap.put(key, value);
        }

        return TRSSubstitution.create(ImmutableCreator.create(newSigmaMap));
    }

    /**
     * @param sigma
     * @return {x/t\theta | x/t \in \sigma}
     */
    public static TRSSubstitution applyInRange(final TRSSubstitution sigma,
        final TRSSubstitution theta) {
        final Map<TRSVariable, TRSTerm> newSigmaMap = new LinkedHashMap<>();

        for (final Entry<TRSVariable, ? extends TRSTerm> mapping : sigma.toMap().entrySet()) {
            newSigmaMap.put(mapping.getKey(),
                mapping.getValue().applySubstitution(theta));
        }

        return TRSSubstitution.create(ImmutableCreator.create(newSigmaMap));
    }

    /**
     * @param sigma
     * @return {x\theta /t| x/t \in \sigma}
     */
    public static TRSSubstitution applyInDomain(final TRSSubstitution sigma,
        final TRSSubstitution theta) {
        final Map<TRSVariable, TRSTerm> newSigmaMap = new LinkedHashMap<>();

        for (final Entry<TRSVariable, ? extends TRSTerm> mapping : sigma.toMap().entrySet()) {
            newSigmaMap.put(
                (TRSVariable) mapping.getKey().applySubstitution(theta),
                mapping.getValue());
        }

        return TRSSubstitution.create(ImmutableCreator.create(newSigmaMap));
    }

    /**
     * Apply rewrite sequence to a term
     *
     * @param toRewrite term to be rewritten
     * @param rewriteSeq the sequence to rewrite the term
     * @param R for checking if the rule is in R
     * @return a pair of the resulting term and a list of intermediate steps.
     *         Please note, that the list of intermediate steps is just for
     *         having the sequence exported to xml properly.
     */
    public static Pair<TRSTerm, List<TRSTerm>> rewriteSequence(TRSTerm toRewrite,
        final List<Pair<Position, Rule>> rewriteSeq,
        final ImmutableSet<Rule> R) {

        final List<TRSTerm> intermediateSteps = new LinkedList<>();
        for (final Pair<Position, Rule> seq : rewriteSeq) {
            intermediateSteps.add(toRewrite);
            final Rule rule = seq.y;

            // must be a rule of R
            if (!R.contains(rule)) {
                if (Globals.DEBUG_NEX) {
                    System.err.println("Rewriting: Rule " + rule
                        + " is not in R!");
                }
                return null;
            }

            final Position pi = seq.x;

            final TRSTerm subterm = toRewrite.getSubterm(pi);
            if (subterm == null) {
                if (Globals.DEBUG_NEX) {
                    System.err.println("Rewriting: Position " + pi
                        + " is not a position of " + toRewrite);
                }
                return null;
            }

            final TRSTerm lhs = rule.getLeft();
            final TRSSubstitution matcher = lhs.getMatcher(subterm);

            toRewrite =
                toRewrite.replaceAt(pi,
                    rule.getRight().applySubstitution(matcher));
        }
        intermediateSteps.add(toRewrite);
        return new Pair<>(toRewrite, intermediateSteps);
    }

    /**
     * Returns a substitution rho such that x sigma rho = x theta for all x in
     * dom(sigma) \cup dom(theta).
     * @param sigma
     * @param theta
     * @return rho or null if no such rho exists.
     */
    public static TRSSubstitution matchSubstitutionsRelaxed(final TRSSubstitution sigma,
        final TRSSubstitution theta) {
        final Map<TRSVariable, TRSTerm> rawRho = new LinkedHashMap<>();
        final Set<TRSVariable> domUnion = new LinkedHashSet<>();
        domUnion.addAll(sigma.getDomain());
        domUnion.addAll(theta.getDomain());
        for (final TRSVariable x : domUnion) {
            final TRSTerm s = sigma.substitute(x);
            final TRSTerm t = theta.substitute(x);
            final TRSSubstitution tau = s.getMatcher(t);
            if (tau == null) {
                return null;
            }
            for (final Entry<TRSVariable, ? extends TRSTerm> e : tau.toMap().entrySet()) {
                if (rawRho.containsKey(e.getKey())) {
                    if (!rawRho.get(e.getKey()).equals(e.getValue())) {
                        return null;
                    }
                } else {
                    rawRho.put(e.getKey(), e.getValue());
                }
            }
        }

        final TRSSubstitution rho = TRSSubstitution.create(ImmutableCreator.create(rawRho));
        if (Globals.useAssertions) {
            assert sigma.compose(rho).restrictTo(domUnion).equals(theta);
        }

        return rho;
    }

    /**
     * Returns a substitution rho such that sigma rho = theta.
     * @param sigma
     * @param theta
     * @return rho or null if no such rho exists.
     */
    public static TRSSubstitution matchSubstitutions(final TRSSubstitution sigma,
        final TRSSubstitution theta) {

        final TRSSubstitution rho = Utils.matchSubstitutionsRelaxed(sigma, theta);

        if (rho == null || !sigma.compose(rho).equals(theta)) {
            return null;
        }
        return rho;
    }

    /**
     * Find a substitution theta such that lSigma theta = rSigma theta.
     * @param lSigma
     * @param rSigma
     * @return theta if it exists, null otherwise.
     */
    public static TRSSubstitution unifySubstitutions(final TRSSubstitution lSigma,
        final TRSSubstitution rSigma) {

        TRSSubstitution theta = TRSSubstitution.EMPTY_SUBSTITUTION;

        final Set<TRSVariable> doms = new LinkedHashSet<>();
        doms.addAll(lSigma.getDomain());
        doms.addAll(rSigma.getDomain());

        for (final TRSVariable x : doms) {
            final TRSTerm l = x.applySubstitution(lSigma).applySubstitution(theta);
            final TRSTerm r = x.applySubstitution(rSigma).applySubstitution(theta);

            final TRSSubstitution mu = l.getMGU(r);
            if (mu == null) {
                return null;
            }
            theta = theta.compose(mu);
        }

        if (Globals.useAssertions) {
            assert lSigma.compose(theta).equals(rSigma.compose(theta));
        }

        return theta;
    }
}
