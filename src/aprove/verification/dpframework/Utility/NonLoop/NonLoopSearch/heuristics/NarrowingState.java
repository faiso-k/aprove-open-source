package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.*;
import aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch.heuristics.NarrowingHeuristic.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.combination.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.eproofs.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import immutables.*;

class NarrowingState {
    ProofedRule plr;
    ProofedRule pst;
    Position pi;
    NarrowingDirection dir;

    @Override
    public String toString() {
        String rv = "T:\n";
        rv += this.getLeftRuleBase() + "\n";
        rv += this.getRightRuleBase() + "\n";
        rv += "Sigma:\n";
        rv += this.plr.getPatternRule().getLhs().getSigma() + " ->\n";
        rv += this.plr.getPatternRule().getRhs().getSigma() + "\n";
        rv += this.pst.getPatternRule().getLhs().getSigma() + " ->\n";
        rv += this.pst.getPatternRule().getRhs().getSigma() + "\n";
        rv += "Mu:\n";
        rv += this.plr.getPatternRule().getLhs().getMu() + " ->\n";
        rv += this.plr.getPatternRule().getRhs().getMu() + "\n";
        rv += this.pst.getPatternRule().getLhs().getMu() + " ->\n";
        rv += this.pst.getPatternRule().getRhs().getMu() + "\n";

        return rv;
    }

    public static ProofedRule narrow(final ProofedRule plr,
        final ProofedRule pst,
        final Position pi,
        final NarrowingDirection dir) {
        final NarrowingState state = new NarrowingState(plr, pst, pi, dir);
        state.normalize();
        return state.makeBasesEqual();
    }

    public NarrowingState(final ProofedRule plr, final ProofedRule pst, final Position pi, final NarrowingDirection dir) {
        this.plr = plr;
        this.pst = pst;
        this.pi = pi;
        this.dir = dir;
    }

    TRSTerm getLeftRuleBase() {
        switch (this.dir) {
        case Forward:
            return this.plr.getPatternRule().getRhs().getT().getSubterm(this.pi);
        case OnlyRoot:
        case Backward:
            return this.plr.getPatternRule().getRhs().getT();
        }
        return null;
    }

    TRSTerm getRightRuleBase() {
        switch (this.dir) {
        case Forward:
        case OnlyRoot:
            return this.pst.getPatternRule().getLhs().getT();
        case Backward:
            return this.pst.getPatternRule().getLhs().getT().getSubterm(this.pi);
        }
        return null;
    }

    void normalize() {
        this.plr = this.plr.getStandardLeft();
        this.pst = this.pst.getStandardRight();
    }

    boolean equalBases() {
        return this.getLeftRuleBase().equals(this.getRightRuleBase());
    }

    boolean equalSigmas() {
        final PatternRule lr = this.plr.getPatternRule();
        final PatternRule st = this.pst.getPatternRule();
        final TRSSubstitution sigma = lr.getLhs().getSigma();
        return sigma.equals(lr.getRhs().getSigma()) && sigma.equals(st.getLhs().getSigma())
            && sigma.equals(st.getRhs().getSigma());

    }

    boolean equalMus() {
        final PatternRule lr = this.plr.getPatternRule();
        final PatternRule st = this.pst.getPatternRule();
        final TRSSubstitution mu = lr.getLhs().getMu();
        return mu.equals(lr.getRhs().getMu()) && mu.equals(st.getLhs().getMu()) && mu.equals(st.getRhs().getMu());
    }

    private static TRSSubstitution[] unclashSubstitutions(final TRSSubstitution... subs) {
        final LinkedHashSet<TRSVariable> domains = new LinkedHashSet<>();
        final TRSSubstitution[] rvs = new TRSSubstitution[subs.length];
        for (int i = 0; i < subs.length; ++i) {
            rvs[i] = TRSSubstitution.EMPTY_SUBSTITUTION;
            domains.addAll(subs[i].getDomain());
        }

        for (final TRSVariable x : domains) {
            TRSTerm t = x;
            for (int i = 0; i < subs.length; ++i) {
                final TRSSubstitution subi = subs[i];
                if (subi.getDomain().contains(x)) {
                    final Pair<TRSSubstitution, TRSSubstitution> thetas = Utils.findSubstitutions(subi.substitute(x), t);

                    if (thetas == null) {
                        continue;
                    }

                    final TRSSubstitution theta2 = thetas.x;
                    final TRSSubstitution theta1 = thetas.y;

                    t = t.applySubstitution(theta1);
                    rvs[i] = rvs[i].compose(theta2);

                    for (int j = 0; j < i; ++j) {
                        if (subs[j].getDomain().contains(x)) {
                            subs[j] = subs[j].compose(theta1);
                            rvs[j] = rvs[j].compose(theta1);
                        }
                    }
                }
            }
        }

        return rvs;
    }

    static TRSSubstitution[] mergeSubstitutions(final TRSSubstitution... subs) {
        final LinkedHashSet<TRSVariable> domains = new LinkedHashSet<>();
        final ArrayList<Map<TRSVariable, TRSTerm>> rvs = new ArrayList<>();
        for (int i = 0; i < subs.length; ++i) {
            domains.addAll(subs[i].getDomain());
            rvs.add(i, new LinkedHashMap<TRSVariable, TRSTerm>());
        }
        for (final TRSVariable x : domains) {
            TRSTerm result = null;
            for (final TRSSubstitution sub : subs) {
                final TRSTerm t = x.applySubstitution(sub);
                if (!x.equals(t)) {
                    if (result == null) {
                        result = t;
                    }
                    if (!t.equals(result)) {
                        return null;
                    }
                }
            }
            assert result != null;
            for (int i = 0; i < subs.length; ++i) {
                if (subs[i].substitute(x).equals(x)) {
                    rvs.get(i).put(x, result);
                }
            }
        }
        final TRSSubstitution[] rsubs = new TRSSubstitution[subs.length];
        for (int i = 0; i < subs.length; ++i) {
            rsubs[i] = TRSSubstitution.create(ImmutableCreator.create(rvs.get(i)));
        }

        return rsubs;
    }

    static Triple<TRSSubstitution, TRSSubstitution, TRSSubstitution> instantiationOrAddUnusedSplit(final TRSSubstitution sigma,
        final Set<TRSVariable> us,
        final TRSSubstitution theta,
        final Set<TRSVariable> ut) {
        final LinkedHashSet<TRSVariable> domains = new LinkedHashSet<>();
        domains.addAll(sigma.getDomain());
        domains.addAll(theta.getDomain());

        final LinkedHashMap<TRSVariable, TRSTerm> instantiate = new LinkedHashMap<TRSVariable, TRSTerm>();
        final LinkedHashMap<TRSVariable, TRSTerm> addUnusedSigma = new LinkedHashMap<TRSVariable, TRSTerm>();
        final LinkedHashMap<TRSVariable, TRSTerm> addUnusedTheta = new LinkedHashMap<TRSVariable, TRSTerm>();

        for (final TRSVariable x : domains) {
            final TRSTerm s = x.applySubstitution(sigma);
            final TRSTerm t = x.applySubstitution(theta);

            final boolean mustInstS = !x.equals(s) && us.contains(x);
            final boolean mustInstT = !x.equals(t) && ut.contains(x);
            final boolean eq = s.equals(t);

            if (mustInstS || mustInstT) {
                if (eq) {
                    instantiate.put(x, s);
                } else {
                    continue; // don't know what to do here
                }
            } else {
                if (!x.equals(t)) {
                    addUnusedTheta.put(x, t);
                }
                if (!x.equals(s)) {
                    addUnusedSigma.put(x, s);
                }
            }
        }

        return new Triple<TRSSubstitution, TRSSubstitution, TRSSubstitution>(
            TRSSubstitution.create(ImmutableCreator.create(instantiate)),
            TRSSubstitution.create(ImmutableCreator.create(addUnusedSigma)),
            TRSSubstitution.create(ImmutableCreator.create(addUnusedTheta)));
    }

    static ProofedRule addToSigmas(ProofedRule st, final TRSSubstitution missingS, final TRSSubstitution missingT) {
        final PatternTerm s = st.getPatternRule().getLhs();
        final PatternTerm t = st.getPatternRule().getRhs();

        final Set<TRSVariable> us = s.getRelevantVariables();
        final Set<TRSVariable> ut = t.getRelevantVariables();

        final Triple<TRSSubstitution, TRSSubstitution, TRSSubstitution> missing =
            NarrowingState.instantiationOrAddUnusedSplit(missingS, us, missingT, ut);
        if (missing == null) {
            return null;
        }
        final TRSSubstitution inst = missing.x;
        final TRSSubstitution sigmaSPrime = missing.y;
        final TRSSubstitution sigmaTPrime = missing.z;

        if (!inst.isEmpty()) {
            st = InstantiateSigma.create(st, inst);
        }
        if (st == null) {
            return null;
        }
        if (!sigmaSPrime.isEmpty() || !sigmaTPrime.isEmpty()) {
            //            st =
            //                AddUnused.create(st, sigmaSPrime, Substitution.EMPTY_SUBSTITUTION, sigmaTPrime,
            //                    Substitution.EMPTY_SUBSTITUTION);

            final PatternTerm lhs = st.getPatternRule().getLhs();
            EquivalenceProof proof =
                EquivIrrelevantPatternSubsProof.create(lhs, true, sigmaSPrime.compose(lhs.getSigma()), lhs.getMu());
            st = Equivalence.create(st, proof);

            if (st == null) {
                return null;
            }

            final PatternTerm rhs = st.getPatternRule().getRhs();
            proof =
                EquivIrrelevantPatternSubsProof.create(rhs, false, sigmaTPrime.compose(rhs.getSigma()), rhs.getMu());
            st = Equivalence.create(st, proof);
        }
        if (st == null) {
            return null;
        }

        return st;
    }

    static ProofedRule addToMus(ProofedRule st, final TRSSubstitution missingS, final TRSSubstitution missingT) {
        final PatternTerm s = st.getPatternRule().getLhs();
        final PatternTerm t = st.getPatternRule().getRhs();

        final Set<TRSVariable> us = s.getRelevantVariables();
        final Set<TRSVariable> ut = t.getRelevantVariables();

        final Triple<TRSSubstitution, TRSSubstitution, TRSSubstitution> missing =
            NarrowingState.instantiationOrAddUnusedSplit(missingS, us, missingT, ut);
        if (missing == null) {
            return null;
        }
        final TRSSubstitution inst = missing.x;
        final TRSSubstitution muSPrime = missing.y;
        final TRSSubstitution muTPrime = missing.z;

        if (!inst.isEmpty()) {
            st = InstantiateMu.create(st, inst);
        }
        if (st == null) {
            return null;
        }
        if (!muSPrime.isEmpty() || !muTPrime.isEmpty()) {
            // st =
            // AddUnused.create(st, Substitution.EMPTY_SUBSTITUTION, muSPrime,
            //                      Substitution.EMPTY_SUBSTITUTION, muTPrime);

            final PatternTerm lhs = st.getPatternRule().getLhs();
            EquivalenceProof proof =
                EquivIrrelevantPatternSubsProof.create(lhs, true, lhs.getSigma(), muSPrime.compose(lhs.getMu()));
            st = Equivalence.create(st, proof);

            if (st == null) {
                return null;
            }

            final PatternTerm rhs = st.getPatternRule().getRhs();
            proof = EquivIrrelevantPatternSubsProof.create(rhs, false, rhs.getSigma(), muTPrime.compose(rhs.getMu()));
            st = Equivalence.create(st, proof);
        }
        if (st == null) {
            return null;
        }

        return st;
    }

    ProofedRule makeMusEqual() {
        {
            final PatternTerm l = this.plr.getPatternRule().getLhs();
            final PatternTerm r = this.plr.getPatternRule().getRhs();
            final PatternTerm s = this.pst.getPatternRule().getLhs();
            final PatternTerm t = this.pst.getPatternRule().getRhs();

            final TRSSubstitution muL = l.getMu();
            final TRSSubstitution muR = r.getMu();
            final TRSSubstitution muS = s.getMu();
            final TRSSubstitution muT = t.getMu();
            final TRSSubstitution[] missing = NarrowingState.unclashSubstitutions(muL, muR, muS, muT);
            if (missing == null) {
                return null;
            }
            final TRSSubstitution missingL = missing[0];
            final TRSSubstitution missingR = missing[1];
            final TRSSubstitution missingS = missing[2];
            final TRSSubstitution missingT = missing[3];

            this.plr = InstantiateMu.create(this.plr, missingL.compose(missingR));
            if (this.plr == null) {
                return null;
            }
            this.pst = InstantiateMu.create(this.pst, missingS.compose(missingT));
            if (this.pst == null) {
                return null;
            }
        }
        {
            final PatternTerm l = this.plr.getPatternRule().getLhs();
            final PatternTerm r = this.plr.getPatternRule().getRhs();
            final PatternTerm s = this.pst.getPatternRule().getLhs();
            final PatternTerm t = this.pst.getPatternRule().getRhs();

            final TRSSubstitution muL = l.getMu();
            final TRSSubstitution muR = r.getMu();
            final TRSSubstitution muS = s.getMu();
            final TRSSubstitution muT = t.getMu();
            final TRSSubstitution[] missing = NarrowingState.mergeSubstitutions(muL, muR, muS, muT);
            if (missing == null) {
                return null;
            }
            final TRSSubstitution missingL = missing[0];
            final TRSSubstitution missingR = missing[1];
            final TRSSubstitution missingS = missing[2];
            final TRSSubstitution missingT = missing[3];

            this.plr = NarrowingState.addToMus(this.plr, missingL, missingR);
            if (this.plr == null) {
                return null;
            }
            this.pst = NarrowingState.addToMus(this.pst, missingS, missingT);
            if (this.pst == null) {
                return null;
            }
        }
        {
            final PatternTerm l = this.plr.getPatternRule().getLhs();
            final PatternTerm r = this.plr.getPatternRule().getRhs();
            final PatternTerm s = this.pst.getPatternRule().getLhs();
            final PatternTerm t = this.pst.getPatternRule().getRhs();

            final TRSSubstitution muL = l.getMu();
            final TRSSubstitution muR = r.getMu();
            final TRSSubstitution muS = s.getMu();
            final TRSSubstitution muT = t.getMu();
            final TRSSubstitution[] missing = NarrowingState.unclashSubstitutions(muL, muR, muS, muT);
            if (missing == null) {
                return null;
            }
            final TRSSubstitution missingL = missing[0];
            final TRSSubstitution missingR = missing[1];
            final TRSSubstitution missingS = missing[2];
            final TRSSubstitution missingT = missing[3];

            this.plr = InstantiateMu.create(this.plr, missingL.compose(missingR));
            if (this.plr == null) {
                return null;
            }
            this.pst = InstantiateMu.create(this.pst, missingS.compose(missingT));
            if (this.pst == null) {
                return null;
            }
        }

        if (!this.equalMus()) {
            return null;
        }
        if (this.dir == NarrowingHeuristic.NarrowingDirection.Backward) {
            return BackwardNarrowing.create(this.plr, this.pst, this.pi);
        }
        return Narrowing.create(this.plr, this.pst, this.pi);
    }

    ProofedRule makeSigmasEqual() {
        {

            final PatternTerm l = this.plr.getPatternRule().getLhs();
            final PatternTerm r = this.plr.getPatternRule().getRhs();
            final PatternTerm s = this.pst.getPatternRule().getLhs();
            final PatternTerm t = this.pst.getPatternRule().getRhs();

            final TRSSubstitution sigmaL = l.getSigma();
            final TRSSubstitution sigmaR = r.getSigma();
            final TRSSubstitution sigmaS = s.getSigma();
            final TRSSubstitution sigmaT = t.getSigma();
            final TRSSubstitution[] missing = NarrowingState.mergeSubstitutions(sigmaL, sigmaR, sigmaS, sigmaT);
            if (missing == null) {
                return null;
            }
            final TRSSubstitution missingL = missing[0];
            final TRSSubstitution missingR = missing[1];
            final TRSSubstitution missingS = missing[2];
            final TRSSubstitution missingT = missing[3];

            this.plr = NarrowingState.addToSigmas(this.plr, missingL, missingR);
            if (this.plr == null) {
                return null;
            }
            this.pst = NarrowingState.addToSigmas(this.pst, missingS, missingT);
            if (this.pst == null) {
                return null;
            }
        }
        {

            final PatternTerm l = this.plr.getPatternRule().getLhs();
            final PatternTerm r = this.plr.getPatternRule().getRhs();
            final PatternTerm s = this.pst.getPatternRule().getLhs();
            final PatternTerm t = this.pst.getPatternRule().getRhs();

            final TRSSubstitution sigmaL = l.getSigma();
            final TRSSubstitution sigmaR = r.getSigma();
            final TRSSubstitution sigmaS = s.getSigma();
            final TRSSubstitution sigmaT = t.getSigma();
            final TRSSubstitution[] missing = NarrowingState.mergeSubstitutions(sigmaL, sigmaR, sigmaS, sigmaT);
            if (missing == null) {
                return null;
            }
        }
        if (!this.equalSigmas()) {
            return null;
        }
        return this.makeMusEqual();
    }

    static ProofedRule repairBase(ProofedRule pr,
        final TRSSubstitution theta,
        final Set<TRSVariable> ownDV,
        final Set<TRSVariable> foreignDV,
        final boolean isLR) {

        final Map<TRSVariable, TRSTerm> instantiate = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> domainRenaming = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> instantiateMu = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> substitute = new LinkedHashMap<>();

        for (final Entry<TRSVariable, ? extends TRSTerm> e : theta.toMap().entrySet()) {
            final TRSVariable x = e.getKey();
            final TRSTerm t = e.getValue();
            final Set<TRSVariable> toDV = t.getVariables();
            toDV.retainAll(ownDV);
            final Set<TRSVariable> tfDV = t.getVariables();
            tfDV.retainAll(foreignDV);

            if (ownDV.contains(x)) {
                if (toDV.size() == 1 ^ tfDV.size() == 1) {
                    TRSVariable y;

                    if (toDV.isEmpty()) {
                        // it's a foreign dv

                        y = tfDV.iterator().next();

                        assert y != null;
                        domainRenaming.put(x, y);
                        if (!t.isVariable()) {
                            final TRSSubstitution dr = TRSSubstitution.create(x, y);
                            final PatternTerm pat =
                                (isLR ? pr.getPatternRule().getRhs() : pr.getPatternRule().getLhs()).getDomainRenamed(dr);
                            final TRSSubstitution mu = pat.getMu();
                            final TRSTerm yMu = y.applySubstitution(mu);
                            final TRSSubstitution matcher = yMu.getMatcher(t.applySubstitution(dr));
                            if (matcher != null) {
                                instantiateMu.putAll(matcher.toMap());
                            }
                        }
                    } else {
                        // it's a dv of t
                        y = toDV.iterator().next();
                        final PatternTerm pat = (isLR ? pr.getPatternRule().getRhs() : pr.getPatternRule().getLhs());

                        final TRSSubstitution sigma = pat.getSigma();
                        final TRSSubstitution mu = pat.getMu();

                        PatternTerm xTerm = new PatternTerm(x, sigma, mu);

                        final Pair<TRSSubstitution, TRSSubstitution> musX = xTerm.findEquivalentMus();
                        xTerm = xTerm.simplifyMu(musX.x, musX.y);
                        xTerm = xTerm.removeIrrelevantPatternSubs();
                        assert xTerm != null;

                        PatternTerm yTerm = new PatternTerm(y, sigma, mu);
                        final Pair<TRSSubstitution, TRSSubstitution> musY = yTerm.findEquivalentMus();
                        yTerm = yTerm.simplifyMu(musY.x, musY.y);
                        yTerm = yTerm.removeIrrelevantPatternSubs();
                        assert yTerm != null;

                        xTerm = xTerm.getDomainRenamed(TRSSubstitution.create(x, y));

                        if (!xTerm.getSigma().equals(yTerm.getSigma())) {
                            return null; // what to do here?
                        }

                        final TRSSubstitution muX = xTerm.getMu();
                        final TRSSubstitution muY = yTerm.getMu();

                        final Set<TRSVariable> doms = new LinkedHashSet<>(muX.getDomain());
                        doms.addAll(muY.getDomain());

                        final Set<Pair<TRSTerm, TRSTerm>> uniSet = new LinkedHashSet<>();
                        for (final TRSVariable v : doms) {
                            uniSet.add(new Pair<TRSTerm, TRSTerm>(v.applySubstitution(muX), v.applySubstitution(muY)));
                        }

                        final Unification uni = new Unification(uniSet);
                        final TRSSubstitution mgu = uni.getMgu();

                        if (mgu == null) {
                            return null;
                        }

                        instantiateMu.putAll(mgu.toMap());
                        substitute.put(x, y);
                    }

                } else {
                    return null; // what to do here?
                }
            } else {
                // if it is not a dv, just instantiate
                if (toDV.isEmpty()) {
                    instantiate.put(x, t);
                } else {
                    instantiateMu.put(x, t);
                }
            }
        }
        pr = Instantiation.create(pr, TRSSubstitution.create(ImmutableCreator.create(instantiate)));
        if (pr == null) {
            return null;
        }
        final TRSSubstitution s = TRSSubstitution.create(ImmutableCreator.create(domainRenaming));
        final TRSSubstitution e = TRSSubstitution.EMPTY_SUBSTITUTION;
        pr = Equivalence.createDomainRenaming(pr, isLR ? e : s, isLR ? s : e);
        if (pr == null) {
            return null;
        }
        pr = InstantiateMu.create(pr, TRSSubstitution.create(ImmutableCreator.create(instantiateMu)));
        if (pr == null) {
            return null;
        }

        final TRSSubstitution subst = TRSSubstitution.create(ImmutableCreator.create(substitute));
        pr = PatternUtils.tryToRename(pr, subst, !isLR);
        if (pr == null) {
            return null;
        }

        pr = SimplifyMuHeuristic.simplifyMu(pr);

        return pr;
    }

    static ProofedRule domainRenamingBase(ProofedRule pr,
        final TRSSubstitution theta,
        final Set<TRSVariable> ownDV,
        final Set<TRSVariable> foreignDV,
        final boolean isLR) {

        final Map<TRSVariable, TRSTerm> domainRenaming = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> instantiation = new LinkedHashMap<>();

        for (final Entry<TRSVariable, ? extends TRSTerm> e : theta.toMap().entrySet()) {
            final TRSVariable x = e.getKey();
            final TRSTerm t = e.getValue();
            final Set<TRSVariable> toDV = t.getVariables();
            toDV.retainAll(ownDV);
            final Set<TRSVariable> tfDV = t.getVariables();
            tfDV.retainAll(foreignDV);
            if (ownDV.contains(x) && (tfDV.size() == 1 || t.isVariable()) && toDV.isEmpty()) {
                TRSVariable y;
                if (t.isVariable()) {
                    y = (TRSVariable) t;
                } else {
                    y = tfDV.iterator().next();
                }
                domainRenaming.put(x, y);
            } else {
                instantiation.put(x, t);
            }
        }
        TRSSubstitution rho = TRSSubstitution.create(ImmutableCreator.create(domainRenaming));
        final TRSSubstitution e = TRSSubstitution.EMPTY_SUBSTITUTION;
        pr = Equivalence.createDomainRenaming(pr, isLR ? e : rho, isLR ? rho : e);
        if (pr == null) {
            return null;
        }
        rho = TRSSubstitution.create(ImmutableCreator.create(instantiation));
        pr = Instantiation.create(pr, rho);
        if (pr == null) {
            return null;
        }
        return pr;
    }

    static ProofedRule baseInstantiate(final ProofedRule pr,
        final TRSVariable x,
        final TRSTerm t,
        final Set<TRSVariable> ownDV,
        final Set<TRSVariable> foreignDV,
        final FreshNameGenerator gen,
        final boolean isLR) {

        final TRSSubstitution id = TRSSubstitution.EMPTY_SUBSTITUTION;

        final Set<TRSVariable> tVars = t.getVariables();
        tVars.retainAll(ownDV);

        if (!ownDV.contains(x)) {
            if (ownDV.contains(t)) {
                // x is not a domain var and t is a domain var
                return NarrowingState.solveNonLinearCase(pr, x, t, ownDV, foreignDV, gen, isLR);
            } else {
                // t is a term or t is a variable but not a domain var
                // try instantiation after renaming the dv in t to new vars
                final Map<TRSVariable, TRSTerm> renaming = new LinkedHashMap<>();
                for (final TRSVariable y : tVars) {
                    renaming.put(y, TRSTerm.createVariable(gen.getFreshName(y.getName(), false)));
                }
                final TRSSubstitution rename = TRSSubstitution.create(ImmutableCreator.create(renaming));

                final ProofedRule inst = Instantiation.create(pr, TRSSubstitution.create(x, t.applySubstitution(rename)));
                if (inst != null) {
                    return inst;
                }
            }
        }

        // x is a domain var
        assert ownDV.contains(x);

        if (t.isVariable()) {
            if (ownDV.contains(t)) { // x and t are domain vars
                // try to instantiate only mu

                // TODO should that be here?
                //                pr = PatternUtils.reduceRenamings(pr, isLR);

                return NarrowingState.solveEqualityGoal(pr, x, (TRSVariable) t, ownDV, foreignDV, gen, isLR);
            } else {
                // x is domain var and t is a variable but not a domain var
                return Equivalence.createDomainRenaming(pr, isLR ? id : TRSSubstitution.create(x, t),
                    isLR ? TRSSubstitution.create(x, t) : id);
            }
        } else { // x is domain var but t is not a var

            //            System.err.println("pr: " + pr);
            //            System.err.println("x: " + x + "  t: " + t);
            //            System.err.println("isLR: " + isLR);

            // assert false;
            return null;
        }
    }

    static ProofedRule baseInstantiate2(ProofedRule pr,
        final TRSSubstitution theta,
        final Set<TRSVariable> ownDV,
        final Set<TRSVariable> foreignDV,
        final boolean isLR) {

        final Map<TRSVariable, TRSTerm> instantiate = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> instantiateMu = new LinkedHashMap<>();

        for (final Entry<TRSVariable, ? extends TRSTerm> e : theta.toMap().entrySet()) {
            final TRSVariable x = e.getKey();
            final TRSTerm t = e.getValue();
            final Set<TRSVariable> toDV = t.getVariables();
            toDV.retainAll(ownDV);
            if (!ownDV.contains(x)) {
                if (toDV.isEmpty()) {
                    instantiate.put(x, t);
                }
            } else {
                instantiateMu.put(x, t);
            }
        }
        final TRSSubstitution rho = TRSSubstitution.create(ImmutableCreator.create(instantiate));
        pr = Instantiation.create(pr, rho);
        if (pr == null) {
            return null;
        }

        if (!instantiateMu.isEmpty()) {
            pr = InstantiateMu.create(pr, TRSSubstitution.create(ImmutableCreator.create(instantiateMu)));
            if (pr == null) {
                return null;
            }
        }
        pr = SimplifyMuHeuristic.simplify(pr, new FreshNameGenerator(new PrefixNameGenerator("w"))); // TODO make this less magical

        return pr;
    }

    static ProofedRule solveNonLinearCase(ProofedRule pr,
        final TRSVariable x,
        final TRSTerm t,
        final Set<TRSVariable> ownDV,
        final Set<TRSVariable> foreignDV,
        final FreshNameGenerator gen,
        final boolean isLR) {
        final Map<TRSVariable, TRSTerm> instantiateMu = new LinkedHashMap<>();

        final PatternTerm r = pr.getPatternRule().getRhs();
        final TRSSubstitution rMu = r.getMu();

        final Set<TRSVariable> toDV = t.getVariables();
        toDV.retainAll(ownDV);

        TRSVariable zl;
        TRSVariable zr;
        TRSTerm tPrime;

        zl = toDV.iterator().next();
        zr = x;
        tPrime = t;
        for (final Entry<TRSVariable, ? extends TRSTerm> entry : rMu.toMap().entrySet()) {
            if (entry.getValue().equals(x)) {
                zr = entry.getKey();
                tPrime = t.applySubstitution(TRSSubstitution.create(zl, zr));
                instantiateMu.put(x, tPrime);
                break;
            }
        }

        // do the InstantateMu, Simplify and InstantateSimga steps
        pr = InstantiateMu.create(pr, TRSSubstitution.create(ImmutableCreator.create(instantiateMu)));
        if (pr == null) {
            return null;
        }
        pr = SimplifyMuHeuristic.simplify(pr, new FreshNameGenerator(new PrefixNameGenerator("w")));
        pr = InstantiateSigma.create(pr, TRSSubstitution.create(zr, tPrime));
        if (pr == null) {
            return null;
        }

        return NarrowingState.solveEqualityGoal(pr, zr, zl, ownDV, foreignDV, gen, isLR);
    }

    static ProofedRule solveEqualityGoal(ProofedRule pr,
        final TRSVariable zr,
        final TRSVariable zl,
        final Set<TRSVariable> ownDV,
        final Set<TRSVariable> foreignDV,
        final FreshNameGenerator gen,
        final boolean isLR) {

        // meet the equalityGoal zr/zl
        final TRSSubstitution id = TRSSubstitution.EMPTY_SUBSTITUTION;
        final PatternTerm pt = isLR ? pr.getPatternRule().getRhs() : pr.getPatternRule().getLhs();
        final TRSSubstitution sigma = pt.getSigma();
        final TRSSubstitution mu = pt.getMu();

        PatternTerm want = new PatternTerm(zl, sigma, mu);
        want = want.removeIrrelevantPatternSubs();
        want = want.getDomainRenamed(TRSSubstitution.create(zl, zr));

        final TRSSubstitution existingSigma = sigma.restrictTo(want.getSigma().getDomain());
        final TRSSubstitution missingSigma = Utils.matchSubstitutionsRelaxed(existingSigma, want.getSigma());
        if (missingSigma == null) {
            return null;
        }
        pr = InstantiateSigma.create(pr, missingSigma);
        if (pr == null) {
            return null;
        }

        final TRSSubstitution existingMu = mu.restrictTo(want.getMu().getDomain());
        final TRSSubstitution missingMu = Utils.matchSubstitutionsRelaxed(existingMu, want.getMu());
        if (missingMu == null) {
            return null;
        }
        pr = InstantiateMu.create(pr, missingMu);
        if (pr == null) {
            return null;
        }

        // now zl and zr should be equal w.r.t. to the current sigma and mu
        final TRSSubstitution eqSub = TRSSubstitution.create(zl, zr);
        pr = PatternUtils.tryToRename(pr, eqSub, !isLR);
        if (pr == null) {
            return null;
        }

        return pr;
    }

    static ProofedRule baseEqualitySubstitute2(ProofedRule pr,
        final TRSSubstitution theta,
        final Set<TRSVariable> ownDV,
        final Set<TRSVariable> foreignDV,
        final boolean isLR) {

        // variable names in this method are chosen according to the following:
        // we need to instantiate {y/s(zl)} in
        // f(s(zl),y){zl/s(zl)}^n{zl/x} -> f(x,s(zr)){zr/s(zr)}^n{zr/y}
        // first, we instantiate mu with {y/s(zr)} (Map instantiateMu)
        // f(s(zl),y){zl/s(zl)}^n{zl/x,y/s(zr)} ->
        // f(x,s(zr)){zr/s(zr)}^n{y/s(zr),zr/s(zr)}
        // then we simplify
        // f(s(zl),s(zr)){zl/s(zl)}^n{zl/x} -> f(x,s(s(zr))){zr/s(zr)}^n
        // then we instantiate sigma with {zr/s(zr)} (Map instantiateSigma)
        // f(s(zl),s(zr)){zl/s(zl),zr/s(zr)}^n{zl/x} ->
        // f(x,s(s(zr))){zr/s(s(zr))}^n

        // then we add {zl=zr} as an equality goal

        // then we need to make zl\sigma^n\mu equal to zr\sigma^n\mu by
        // Instantiate Mu with {zr/x}
        // f(s(zl),s(zr)){zl/s(zl),zr/s(zr)}^n{zl/x,zr/x} ->
        // f(x,s(s(zr))){zr/s(s(zr))}^n{zr/x}
        // and finally equality substitute zr by zl on the LHS:
        // f(s(zl),s(zl)){zl/s(zl),zr/s(zr)}^n{zl/x,zr/x} ->
        // f(x,s(s(zr))){zr/s(s(zr))}^n{zr/x}
        // one further simplify yields
        // f(s(zl),s(zl)){zl/s(zl)}^n{zl/x} ->
        // f(x,s(s(zr))){zr/s(s(zr))}^n{zr/x}

        final Map<TRSVariable, TRSTerm> instantiateMu = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> instantiateSigma = new LinkedHashMap<>();
        final Map<TRSVariable, TRSTerm> equalityGoals = new LinkedHashMap<>();
        {
            final PatternTerm r = pr.getPatternRule().getRhs();
            final TRSSubstitution rMu = r.getMu();

            for (final Entry<TRSVariable, ? extends TRSTerm> e : theta.toMap().entrySet()) {
                final TRSVariable y = e.getKey();
                final TRSTerm t = e.getValue();
                final Set<TRSVariable> toDV = t.getVariables();
                toDV.retainAll(ownDV);

                if (!ownDV.contains(y) && toDV.size() == 1) {
                    final TRSVariable zl = toDV.iterator().next();
                    TRSVariable zr = y;
                    TRSTerm tPrime = t;
                    for (final Entry<TRSVariable, ? extends TRSTerm> entry : rMu.toMap().entrySet()) {
                        if (entry.getValue().equals(y)) {
                            zr = entry.getKey();
                            tPrime = t.applySubstitution(TRSSubstitution.create(zl, zr));
                            instantiateMu.put(y, tPrime);
                            break;
                        }
                    }

                    instantiateSigma.put(zr, tPrime);
                    equalityGoals.put(zl, zr);
                    // } else {
                    // // don't forget about this goal
                    // equalityGoals.put(y, t);
                }
            }
        }
        // do the InstantateMu, Simplify and InstantateSimga steps
        {
            pr = InstantiateMu.create(pr, TRSSubstitution.create(ImmutableCreator.create(instantiateMu)));
            if (pr == null) {
                return null;
            }
            pr = SimplifyMuHeuristic.simplify(pr, new FreshNameGenerator(new PrefixNameGenerator("w")));
            pr = InstantiateSigma.create(pr, TRSSubstitution.create(ImmutableCreator.create(instantiateSigma)));
            if (pr == null) {
                return null;
            }
        }
        // meet the equalityGoals
        {
            final TRSSubstitution id = TRSSubstitution.EMPTY_SUBSTITUTION;
            TRSSubstitution missingSigma = id;
            TRSSubstitution missingMu = id;
            final PatternTerm pt = isLR ? pr.getPatternRule().getRhs() : pr.getPatternRule().getLhs();
            for (final Entry<TRSVariable, TRSTerm> e : equalityGoals.entrySet()) {
                final TRSVariable zl = e.getKey();
                final TRSVariable zr = (TRSVariable) e.getValue();
                final TRSSubstitution sigma = pt.getSigma().compose(missingSigma);
                final TRSSubstitution mu = pt.getMu().compose(missingMu);

                PatternTerm zlp = new PatternTerm(zl, sigma, mu);
                PatternTerm zrp = new PatternTerm(zr, sigma, mu);
                zlp = zlp.removeIrrelevantPatternSubs();
                zrp = zrp.removeIrrelevantPatternSubs();
                zlp = zlp.getDomainRenamed(TRSSubstitution.create(zl, zr));

                final TRSSubstitution lSigma = zlp.getSigma();
                final TRSSubstitution rSigma = zrp.getSigma();

                if (!lSigma.equals(rSigma)) {
                    final TRSSubstitution rho = NarrowingState.unifySubstitutions(lSigma, rSigma);
                    if (rho == null) {
                        return null;
                    }
                    missingSigma = missingSigma.compose(rho);

                }
                final TRSSubstitution lMu = zlp.getMu();
                final TRSSubstitution rMu = zrp.getMu();

                if (!lMu.equals(rMu)) {
                    final TRSSubstitution rho = NarrowingState.unifySubstitutions(lMu, rMu);
                    if (rho == null) {
                        return null;
                    }
                    missingMu = missingMu.compose(rho);
                }
            }

            // try to instantiate the missing parts
            pr = InstantiateSigma.create(pr, missingSigma);
            if (pr == null) {
                return null;
            }
            pr = InstantiateMu.create(pr, missingMu);
            if (pr == null) {
                return null;
            }

            // now zl and zr should be equal w.r.t. to the current sigma and mu
            // lets try to apply the Equality Substitution
            final TRSSubstitution eqSub = TRSSubstitution.create(ImmutableCreator.create(equalityGoals));
            pr = PatternUtils.tryToRename(pr, eqSub, !isLR);
            if (pr == null) {
                return null;
            }
        }

        return pr;
    }

    /**
     * Find a substitution theta such that lSigma theta = rSigma theta.
     *
     * @param lSigma
     * @param rSigma
     * @return theta if it exists, null otherwise.
     */
    private static TRSSubstitution unifySubstitutions(final TRSSubstitution lSigma, final TRSSubstitution rSigma) {

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

    /**
     * Find two substitutions lTheta and rTheta such that lSigma lTheta = rSigma
     * rTheta.
     *
     * @param lSigma
     * @param rSigma
     * @return (lTheta, rTheta) if they exist, null otherwise.
     */
    private static Pair<TRSSubstitution, TRSSubstitution> disjointUnifySubstitutions(final TRSSubstitution lSigma,
        final TRSSubstitution rSigma) {

        TRSSubstitution lTheta = TRSSubstitution.EMPTY_SUBSTITUTION;
        TRSSubstitution rTheta = TRSSubstitution.EMPTY_SUBSTITUTION;

        final Set<TRSVariable> doms = new LinkedHashSet<>();
        doms.addAll(lSigma.getDomain());
        doms.addAll(rSigma.getDomain());

        for (final TRSVariable x : doms) {
            final TRSTerm l = x.applySubstitution(lSigma).applySubstitution(lTheta);
            final TRSTerm r = x.applySubstitution(rSigma).applySubstitution(rTheta);

            final Pair<TRSSubstitution, TRSSubstitution> subs = Utils.findSubstitutions(l, r);

            lTheta = lTheta.compose(subs.x);
            rTheta = rTheta.compose(subs.y);
        }

        if (Globals.useAssertions) {
            assert lSigma.compose(lTheta).equals(rSigma.compose(rTheta));
        }

        return new Pair<TRSSubstitution, TRSSubstitution>(lTheta, rTheta);
    }

    public ProofedRule makeBasesEqual() {

        final Set<TRSVariable> forbidden = new LinkedHashSet<>();
        forbidden.addAll(this.plr.getPatternRule().getAllVariables());
        forbidden.addAll(this.pst.getPatternRule().getAllVariables());

        final FreshNameGenerator gen = new FreshNameGenerator(forbidden, new PrefixNameGenerator("w"));

        while (true) {

            final Pair<TRSSubstitution, TRSSubstitution> t = this.getBaseSubstitutions();
            if (t == null) {
                return null;
            }

            final TRSSubstitution thetaR = t.x;
            final TRSSubstitution thetaS = t.y;

            final Set<TRSVariable> dvR = this.plr.getPatternRule().getRhs().getDomainVariables();
            final Set<TRSVariable> dvS = this.pst.getPatternRule().getLhs().getDomainVariables();

            if (!thetaR.isEmpty()) {
                final Entry<TRSVariable, ? extends TRSTerm> xt = thetaR.toMap().entrySet().iterator().next();
                this.plr = NarrowingState.baseInstantiate(this.plr, xt.getKey(), xt.getValue(), dvR, dvS, gen, true);

                if (this.plr == null) {
                    return null;
                }
                this.plr = SimplifyMuHeuristic.simplify(this.plr, gen);
                continue;
            }

            if (!thetaS.isEmpty()) {
                final Entry<TRSVariable, ? extends TRSTerm> xt = thetaS.toMap().entrySet().iterator().next();
                this.pst = NarrowingState.baseInstantiate(this.pst, xt.getKey(), xt.getValue(), dvS, dvR, gen, false);

                if (this.pst == null) {
                    return null;
                }
                this.pst = SimplifyMuHeuristic.simplify(this.pst, gen);
                continue;
            }

            break;
        }

        return this.makeSigmasEqual();
    }

    ProofedRule makeBasesEqual2() {
        final Pair<TRSSubstitution, TRSSubstitution> t = this.getBaseSubstitutions();
        if (t == null) {
            return null;
        }
        final TRSSubstitution thetaR = t.x;
        final TRSSubstitution thetaS = t.y;
        final Set<TRSVariable> dvR = this.plr.getPatternRule().getRhs().getDomainVariables();
        final Set<TRSVariable> dvS = this.pst.getPatternRule().getLhs().getDomainVariables();
        /*
        // Instantiate
        if (!thetaR.isEmpty()) {
            this.plr = baseInstantiate(plr, thetaR, dvR, dvS, true);
            if (this.plr == null) {
                return null;
            }
        }
        if (!thetaS.isEmpty()) {
            pst = baseInstantiate(pst, thetaS, dvS, dvR, false);
            if (this.pst == null) {
                return null;
            }
        }
        // Equality Substitute
        if (!thetaR.isEmpty()) {
            this.plr = baseEqualitySubstitute(plr, thetaR, dvR, dvS, true);
            if (this.plr == null) {
                return null;
            }
        }
        if (!thetaS.isEmpty()) {
            this.pst = baseEqualitySubstitute(pst, thetaS, dvS, dvR, false);
            if (this.pst == null) {
                return null;
            }
        }
        */
        this.normalize();
        // Domain Rename
        if (!thetaR.isEmpty()) {
            this.plr = NarrowingState.domainRenamingBase(this.plr, thetaR, dvR, dvS, true);
            if (this.plr == null) {
                return null;
            }
        }
        if (!thetaS.isEmpty()) {
            this.pst = NarrowingState.domainRenamingBase(this.pst, thetaS, dvS, dvR, false);
            if (this.pst == null) {
                return null;
            }
        }
        if (!this.equalBases()) {
            return null;
        }
        return this.makeSigmasEqual();
    }

    static Integer termDistance(final TRSTerm s, final TRSTerm t) {
        final TRSSubstitution sigma = s.getMGU(t);
        if (sigma == null) {
            return null;
        }

        int i = 0;
        for (final TRSTerm u : sigma.toMap().values()) {
            i += u.getSize() + 1;
        }

        return i;
    }

    Pair<TRSSubstitution, TRSSubstitution> getBaseSubstitutions() {
        final PatternTerm r = this.plr.getPatternRule().getRhs();
        final PatternTerm s = this.pst.getPatternRule().getLhs();

        final TRSSubstitution rSigma = r.getSigma();
        final TRSSubstitution sSigma = s.getSigma();

        final TRSTerm rBase = this.getLeftRuleBase();
        final TRSTerm sBase = this.getRightRuleBase();

        int rExpands = 0;
        int sExpands = 0;
        TRSTerm rBaseExp = rBase;
        TRSTerm sBaseExp = sBase;
        Integer dist = NarrowingState.termDistance(rBaseExp, sBaseExp);
        if (dist == null) {
            return null;
        }

        if (!Options.certifier.isCpf()) {
            // yes we need expand sigma. See class ExpandSigma for more details.
            while (true) {
                final TRSTerm nextExp = rBaseExp.applySubstitution(rSigma);
                final Integer ndist = NarrowingState.termDistance(nextExp, sBaseExp);
                if (ndist != null && ndist < dist) {
                    ++rExpands;
                    rBaseExp = nextExp;
                    dist = ndist;
                } else {
                    break;
                }
            }

            while (true) {
                final TRSTerm nextExp = sBaseExp.applySubstitution(sSigma);
                final Integer ndist = NarrowingState.termDistance(rBaseExp, nextExp);
                if (ndist != null && ndist < dist) {
                    ++sExpands;
                    sBaseExp = nextExp;
                    dist = ndist;
                } else {
                    break;
                }
            }

            this.plr = ExpandSigma.create(this.plr, rExpands);
            this.pst = ExpandSigma.create(this.pst, sExpands);
        }

        final Pair<TRSSubstitution, TRSSubstitution> substs = Utils.findSubstitutions(rBaseExp, sBaseExp);

        final ImmutableMap<TRSVariable, ? extends TRSTerm> thetaR = substs.x.toMap();
        final ImmutableMap<TRSVariable, ? extends TRSTerm> thetaS = substs.y.toMap();

        final LinkedHashMap<TRSVariable, TRSTerm> newThetaR = new LinkedHashMap<>(thetaR);
        final LinkedHashMap<TRSVariable, TRSTerm> newThetaS = new LinkedHashMap<>(thetaS);

        final Set<TRSVariable> dv = new LinkedHashSet<>();
        dv.addAll(this.plr.getPatternRule().getRhs().getDomainVariables());
        dv.addAll(this.pst.getPatternRule().getLhs().getDomainVariables());

        // for (Entry<Variable, ? extends Term> e : thetaR.entrySet()) {
        // if (!e.getValue().isVariable()) {
        // continue;
        // }
        // if (dv.contains(e.getKey()) && !dv.contains(e.getValue())) {
        // newThetaR.remove(e.getKey());
        // newThetaS.put((Variable) e.getValue(), e.getKey());
        // }
        // }
        //
        // for (Entry<Variable, ? extends Term> e : thetaS.entrySet()) {
        // if (!e.getValue().isVariable()) {
        // continue;
        // }
        // if (dv.contains(e.getKey()) && !dv.contains(e.getValue())) {
        // newThetaS.remove(e.getKey());
        // newThetaR.put((Variable) e.getValue(), e.getKey());
        // }
        // }

        return new Pair<TRSSubstitution, TRSSubstitution>(TRSSubstitution.create(ImmutableCreator.create(newThetaR)),
            TRSSubstitution.create(ImmutableCreator.create(newThetaS)));
    }
}
