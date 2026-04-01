package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.DPProblem.Processors.NonTerminationProcessor.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.combination.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.creation.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.nontermination.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class InfRuleLoopProof extends NonTerminationLoopProof {

    private final NonLoopProof po;

    public InfRuleLoopProof(final QDPProblem qdpProblem, final NarrowPair narrowPair,
            final Pair<TRSSubstitution, TRSSubstitution> subst, final Direction dir, final BasicObligation origObl) {
        super(qdpProblem, narrowPair, subst, dir, origObl);
        this.po = Direction.LEFT.equals(dir) ? this.buildProofObjectLeft() : this.buildProofObjectRight();
    }

    private NonLoopProof buildProofObjectLeft() {
        final ImmutableSet<Rule> R = this.qdpProblem.getR();
        final ImmutableSet<Rule> P = this.qdpProblem.getP();

        final LinkedHashMap<Rule, ProofedRule> originals = new LinkedHashMap<>();

        ProofedRule pr = RuleFromTRS.create(this.narrowPair.dp, R, P);

        for (final Triple<Rule, Position, Trs> actTriple : this.narrowPair.getNarrowList()) {
            final Rule lr = actTriple.x;
            final Position pi = actTriple.y;
            ProofedRule narrowRule = originals.get(lr);

            if (narrowRule == null) {
                narrowRule = RuleFromTRS.create(lr, R, P);
                narrowRule = narrowRule.getStandardRight();
                originals.put(lr, narrowRule);
            }
            pr = pr.getStandardLeft();

            final TRSTerm lPi = pr.getPatternRule().getLhs().getT().getSubterm(pi);
            final TRSSubstitution sigma = lPi.getMGU(narrowRule.getPatternRule().getRhs().getT());

            pr = Instantiation.create(pr, sigma);
            final ProofedRule npr = Instantiation.create(narrowRule, sigma);
            pr = BackwardNarrowing.create(npr, pr, pi);
        }

        final PatternRule prule = pr.getPatternRule();
        final SemiUnification su = new SemiUnification(prule.getLhs().getT(), prule.getRhs().getT());

        final Pair<TRSSubstitution, TRSSubstitution> subs = su.getSubstitutions();
        final TRSSubstitution delta1 = subs.y;
        final TRSSubstitution delta2 = subs.x;

        final TRSSubstitution id = TRSSubstitution.EMPTY_SUBSTITUTION;
        pr = Instantiation.create(pr, delta1);
        pr = InstantiateMu.create(pr, delta2);
        pr = Equivalence.createSimplifyingMu(pr, delta2, id, id, delta2);

        return NonLoopProof.create(pr, Position.create(), 0, 0, id, delta2);
    }

    private NonLoopProof buildProofObjectRight() {
        final ImmutableSet<Rule> R = this.qdpProblem.getR();
        final ImmutableSet<Rule> P = this.qdpProblem.getP();

        final LinkedHashMap<Rule, ProofedRule> originals = new LinkedHashMap<>();

        ProofedRule pr = RuleFromTRS.create(this.narrowPair.dp, R, P);

        for (final Triple<Rule, Position, Trs> actTriple : this.narrowPair.getNarrowList()) {
            final Rule lr = actTriple.x;
            final Position pi = actTriple.y;
            ProofedRule narrowRule = originals.get(lr);

            if (narrowRule == null) {
                narrowRule = RuleFromTRS.create(lr, R, P);
                narrowRule = narrowRule.getStandardRight();
                originals.put(lr, narrowRule);
            }
            pr = pr.getStandardLeft();

            final TRSTerm rPi = pr.getPatternRule().getRhs().getT().getSubterm(pi);
            final TRSSubstitution sigma = rPi.getMGU(narrowRule.getPatternRule().getLhs().getT());

            pr = Instantiation.create(pr, sigma);
            final ProofedRule npr = Instantiation.create(narrowRule, sigma);
            pr = Narrowing.create(pr, npr, pi);
        }

        final PatternRule prule = pr.getPatternRule();
        final SemiUnification su = new SemiUnification(prule.getLhs().getT(), prule.getRhs().getT());

        final Pair<TRSSubstitution, TRSSubstitution> subs = su.getSubstitutions();
        final TRSSubstitution delta1 = subs.y;
        final TRSSubstitution delta2 = subs.x;

        final TRSSubstitution id = TRSSubstitution.EMPTY_SUBSTITUTION;
        pr = Instantiation.create(pr, delta1);
        pr = InstantiateMu.create(pr, delta2);
        pr = Equivalence.createSimplifyingMu(pr, delta2, id, id, delta2);

        return NonLoopProof.create(pr, Position.create(), 0, 0, id, delta2);
    }

    @Override
    public String export(final Export_Util eu, final VerbosityLevel level) {
        return this.po.export(eu, level);
    }
}
