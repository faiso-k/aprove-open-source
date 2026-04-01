package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.combination;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class BackwardNarrowing extends ProofedRule {

    /**
     * The left parent used for narrowing
     */
    private final ProofedRule leftParent;

    /**
     * The right parent used for narrowing
     */
    private final ProofedRule rightParent;

    /**
     * Position of narrowing
     */
    private final Position pi;

    private BackwardNarrowing(final PatternTerm lhs, final PatternTerm rhs, final Position piArg,
            final boolean hasPStep, final ProofedRule leftParentArg, final ProofedRule rightParentArg) {
        super(lhs, rhs, leftParentArg.getR(), leftParentArg.getP(), hasPStep);
        this.pi = piArg;
        this.leftParent = leftParentArg;
        this.rightParent = rightParentArg;
        this.setShowRule();
    }

    public static ProofedRule create(final ProofedRule lr, final ProofedRule uv, final Position pi) {
        if (lr.getR() != uv.getR() || lr.getP() != uv.getP()) {
            return null;
        }

        final PatternRule plr = lr.getPatternRule();
        final PatternTerm lhslr = plr.getLhs();
        final PatternTerm rhslr = plr.getRhs();

        final TRSTerm r = rhslr.getT();
        final TRSTerm l = lhslr.getT();

        final TRSSubstitution sigmaL = lhslr.getSigma();
        final TRSSubstitution muL = lhslr.getMu();

        final PatternRule puv = uv.getPatternRule();
        final PatternTerm lhsuv = puv.getLhs();
        final PatternTerm rhsuv = puv.getRhs();
        final TRSTerm u = lhsuv.getT();

        // all sigmas are equal
        if (!(sigmaL.equals(rhslr.getSigma()) && sigmaL.equals(lhsuv.getSigma()) && sigmaL.equals(rhsuv.getSigma()))) {
            return null;
        }
        // all mus are equal
        if (!(muL.equals(rhslr.getMu()) && muL.equals(lhsuv.getMu()) && muL.equals(rhsuv.getMu()))) {
            return null;
        }

        if (r.equals(u.getSubterm(pi))) {
            final PatternTerm lhsN = new PatternTerm(u.replaceAt(pi, l), sigmaL, muL);

            return new BackwardNarrowing(lhsN, rhsuv, pi, lr.hasPStep() || uv.hasPStep(), lr, uv);
        }
        return null;
    }
    
    @Override
    public int getProofStepCount() {
        return 1 + this.leftParent.getProofStepCount() + this.rightParent.getProofStepCount();
    }

    @Override
    public ImmutableList<Pair<Position, Rule>> reconstructSequence() {
        ArrayList<Pair<Position, Rule>> res = new ArrayList<Pair<Position, Rule>>();
        ImmutableList<Pair<Position, Rule>> firstRewriteSeq = leftParent.reconstructSequence();
        ImmutableList<Pair<Position, Rule>> secondRewriteSeq = rightParent.reconstructSequence();

        for(Pair<Position, Rule> step : firstRewriteSeq) {
            res.add(new Pair<>(pi.append(step.x), step.y));
        }

        res.addAll(secondRewriteSeq);
                
        return ImmutableCreator.create(res);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProof(final Export_Util eu) {
        return "Backward-Narrowing at position: " + this.pi.export(eu);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProofShort(final Export_Util eu) {
        return "Backward-Narrowing";
    }

    /**
     * @return The {@link ProofedRule leftParent} for narrowing.
     */
    public ProofedRule getLeftParent() {
        return this.leftParent;
    }

    /**
     * @return The {@link ProofedRule rightParent} for narrowing.
     */
    public ProofedRule getRightParent() {
        return this.rightParent;
    }

    /**
     * @return The {@link Position} for narrowing in the lhs of
     *         {@link ProofedRule rightParent}.
     */
    public Position getPi() {
        return this.pi;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportParents(final Export_Util eu,
        final String indent,
        final String addIndent,
        final boolean firstIntermediate,
        final boolean fullProof) {

        final StringBuilder sb = new StringBuilder();
        sb.append(this.rightParent.export(eu, indent, addIndent, firstIntermediate, fullProof));
        sb.append(eu.linebreak());
        sb.append(this.leftParent.export(eu, indent, addIndent, firstIntermediate, fullProof));

        return sb.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        throw new UnsupportedOperationException("BackwardNarrowing not certifiable.");
    }

}
