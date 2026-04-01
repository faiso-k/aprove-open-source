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

public class Narrowing extends ProofedRule {

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

    private Narrowing(final PatternTerm lhs, final PatternTerm rhs, final Position piArg, final boolean hasPStep,
            final ProofedRule leftParentArg, final ProofedRule rightParentArg) {
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
        final PatternTerm l = plr.getLhs();
        final PatternTerm r = plr.getRhs();
        final PatternRule puv = uv.getPatternRule();
        final PatternTerm u = puv.getLhs();
        final PatternTerm v = puv.getRhs();

        final TRSTerm rBase = r.getT();
        final TRSTerm uBase = u.getT();

        final TRSSubstitution lSigma = l.getSigma();
        final TRSSubstitution lMu = l.getMu();

        if (!rBase.getSubterm(pi).equals(uBase)) {
            return null;
        }

        // all sigmas are equal
        if (!(lSigma.equals(r.getSigma()) && lSigma.equals(u.getSigma()) && lSigma.equals(v.getSigma()))) {
            return null;
        }

        // all mus are equal
        if (!(lMu.equals(r.getMu()) && lMu.equals(u.getMu()) && lMu.equals(v.getMu()))) {
            return null;
        }

        final TRSTerm vBase = v.getT();
        final PatternTerm rhsN = new PatternTerm(rBase.replaceAt(pi, vBase), lSigma, lMu);
        return new Narrowing(l, rhsN, pi, lr.hasPStep() || uv.hasPStep(), lr, uv);
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
        
        res.addAll(firstRewriteSeq);

        for(Pair<Position, Rule> step : secondRewriteSeq) {
            res.add(new Pair<>(pi.append(step.x), step.y));
        }
                
        return ImmutableCreator.create(res);
    }

    @Override
    public String exportProof(final Export_Util eu) {
        return "Narrowing at position: " + this.pi.export(eu);
    }

    @Override
    public String exportProofShort(final Export_Util eu) {
        return "Narrowing at position: " + this.pi.export(eu);
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
     * @return The {@link Position} for narrowing in the rhs of
     *         {@link ProofedRule leftParent}.
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
        sb.append(this.leftParent.export(eu, indent, addIndent, firstIntermediate, fullProof));
        sb.append(eu.linebreak());
        sb.append(this.rightParent.export(eu, indent, addIndent, firstIntermediate, fullProof));

        return sb.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element narrowing = XMLTag.NARROWING.createElement(doc);
        narrowing.appendChild(this.getPatternRule().toDOM(doc, xmlMetaData));
        narrowing.appendChild(this.leftParent.toDOM(doc, xmlMetaData));
        narrowing.appendChild(this.rightParent.toDOM(doc, xmlMetaData));
        narrowing.appendChild(this.pi.toDOM(doc, xmlMetaData));
        final Element proofedRule = XMLTag.PROOFED_RULE.createElement(doc);
        proofedRule.appendChild(narrowing);
        return proofedRule;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element narrowing = CPFTag.NARROWING.createElement(doc);
        narrowing.appendChild(this.leftParent.toCPF(doc, xmlMetaData));
        narrowing.appendChild(this.rightParent.toCPF(doc, xmlMetaData));
        narrowing.appendChild(this.pi.toCPF(doc, xmlMetaData));
        final Element proofedRule = CPFTag.PATTERN_RULE.createElement(doc);
        proofedRule.appendChild(this.getPatternRule().getLhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(this.getPatternRule().getRhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(narrowing);
        return proofedRule;
    }

}
