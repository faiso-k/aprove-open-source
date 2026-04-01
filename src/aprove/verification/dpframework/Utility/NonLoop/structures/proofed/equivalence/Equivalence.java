package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.eproofs.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * ProofedRule by Equivalence of PatternTerms.
 *
 * @author Tim Enger
 */

public final class Equivalence extends ProofedRule {

    /**
     * The proof that shows the Equivalence transformation.
     */
    private final EquivalenceProof eProof;

    /**
     * The parent for this equivalence transformation.
     */
    private final ProofedRule parent;

    /**
     * Constructor
     *
     * @param lhs
     *            The new {@link PatternTerm rhs}.
     * @param rhs
     *            The new {@link PatternTerm rhs}.
     * @param r
     *            The {@link ImmutableSet} R.
     * @param p
     *            The {@link ImmutableSet} P.
     * @param hasPStep
     *            Indicates if there were P-steps
     * @param parentArg
     *            The parent of the new {@link ProofedRule}.
     * @param proof
     *            The corresponding {@link EquivalenceProof proof}.
     */
    private Equivalence(final PatternTerm lhs, final PatternTerm rhs, final ImmutableSet<Rule> r,
            final ImmutableSet<Rule> p, final boolean hasPStep, final ProofedRule parentArg,
            final EquivalenceProof proof) {
        super(lhs, rhs, r, p, hasPStep);
        this.parent = parentArg;
        this.eProof = proof;
    }

    /**
     * Factory Method: Equivalence
     *
     * @param lr
     *            The {@link ProofedRule} whose lhs or rhs was transformed.
     * @param proof
     *            The corresponding {@link EquivalenceProof} for the
     *            transformation.
     * @return A new {@link ProofedRule} that corresponds to the transformation
     *         of {@link ProofedRule lr} according to the
     *         {@link EquivalenceProof proof}. <tt>Null</tt>, if the
     *         {@link EquivalenceProof proof} was <tt>null</tt>. The original
     *         lre is returned, if nothing changes due to the proof.
     */
    public static ProofedRule create(final ProofedRule lr, final EquivalenceProof proof) {
        if (proof == null) {
            return null;
        }

        final PatternTerm before = proof.getTermBefore();
        final PatternRule plr = lr.getPatternRule();

        PatternTerm lhsNew;
        PatternTerm rhsNew;

        if (proof.isLHS()) {
            if (!before.equals(plr.getLhs())) {
                if (Globals.DEBUG_NEX) {
                    System.err.println("Wrong Proof for Equivalence");
                }
                return null;
            }

            lhsNew = proof.getTermAfter();
            rhsNew = plr.getRhs();
        } else {
            if (!before.equals(plr.getRhs())) {
                if (Globals.DEBUG_NEX) {
                    System.err.println("Wrong Proof for Equivalence");
                }
                return null;
            }

            lhsNew = plr.getLhs();
            rhsNew = proof.getTermAfter();
        }

        // check if the rule really changed, otherwise return the old one
        final PatternTerm lhsOld = plr.getLhs();
        final PatternTerm rhsOld = plr.getRhs();

        if (lhsOld.equals(lhsNew) && rhsOld.equals(rhsNew)) {
            return lr;
        }

        return new Equivalence(lhsNew, rhsNew, lr.getR(), lr.getP(), lr.hasPStep(), lr, proof);
    }

    /**
     * Removes all irrelevant (not used) variables from the {@link TRSSubstitution
     * substitutions} of {@link ProofedRule} lr.<br>
     * Therefore, first all the "relevant" {@link TRSSubstitution substitutions}
     * for the lhs are computed and a {@link EquivIrrelevantPatternSubsProof
     * proof} is created. Then, the same is done for the rhs.
     *
     * @param lr
     *            The {@link PatternRule} in which all irrelevant substitutions
     *            should be removed.
     * @return The new {@link PatternRule} in which all irrelevant substitutions
     *         should are removed.If nothing changed, the original
     *         {@link ProofedRule lr} is returned.
     */
    public static ProofedRule createRemoveAllIrrelevant(final ProofedRule lr) {

        // first remove all unused vars form the lhs
        final PatternTerm lhs = lr.getPatternRule().getLhs();
        Pair<TRSSubstitution, TRSSubstitution> subs = lhs.getOnlyRelevantPatternSubs();
        EquivIrrelevantPatternSubsProof proof = EquivIrrelevantPatternSubsProof.create(lhs, true, subs.x, subs.y);
        final ProofedRule lhsRemoved = Equivalence.create(lr, proof);

        // first remove all unused vars form the rhs
        final PatternTerm rhs = lhsRemoved.getPatternRule().getRhs();
        subs = rhs.getOnlyRelevantPatternSubs();
        proof = EquivIrrelevantPatternSubsProof.create(rhs, false, subs.x, subs.y);
        final ProofedRule rhsRemoved = Equivalence.create(lhsRemoved, proof);

        return rhsRemoved;
    }

    /**
     * Apply "Equivalence by Domain Renaming" to a {@link ProofedRule} lr.
     *
     * @param lr
     *            The {@link ProofedRule} to apply to.
     * @param drL
     *            The {@link TRSSubstitution domain renaming} for the lhs.
     * @param drR
     *            The {@link TRSSubstitution domain renaming} for the rhs.
     * @return The domain renamed new {@link ProofedRule}, with separate
     *         {@link EquivDomainRenamingProof proofs} for each domain renaming.
     *         If nothing changed, the original {@link ProofedRule lr} is
     *         returned.
     */
    public static ProofedRule createDomainRenaming(final ProofedRule lr, final TRSSubstitution drL, final TRSSubstitution drR) {

        ProofedRule newpr = lr;
        EquivDomainRenamingProof proof;

        if (!drL.isEmpty()) {
            final PatternTerm lhs = newpr.getPatternRule().getLhs();
            proof = EquivDomainRenamingProof.create(lhs, true, drL);

            if (proof == null) {
                return null;
            }

            newpr = Equivalence.create(newpr, proof);
        }

        if (!drR.isEmpty()) {
            final PatternTerm rhs = newpr.getPatternRule().getRhs();
            proof = EquivDomainRenamingProof.create(rhs, false, drR);

            if (proof == null) {
                return null;
            }

            newpr = Equivalence.create(newpr, proof);
        }

        return newpr;
    }

    /**
     * Apply "Equivalence by Simplifying mu" to a {@link ProofedRule} lr.
     *
     * @param lr
     *            The {@link ProofedRule} to apply to.
     * @param mu1L
     *            {@link TRSSubstitution mu1} for lhs.
     * @param mu2L
     *            {@link TRSSubstitution mu2} for lhs.
     * @param mu1R
     *            {@link TRSSubstitution mu1} for rhs.
     * @param mu2R
     *            {@link TRSSubstitution mu2} for rhs.
     * @return The simplified {@link ProofedRule}. If nothing changed, the
     *         original {@link ProofedRule lr} is returned.
     */
    public static ProofedRule createSimplifyingMu(final ProofedRule lr,
        final TRSSubstitution mu1L,
        final TRSSubstitution mu2L,
        final TRSSubstitution mu1R,
        final TRSSubstitution mu2R) {

        ProofedRule newpr = lr;
        EquivSimplifyingMuProof proof;

        if (!mu1L.isEmpty()) {
            final PatternTerm lhs = newpr.getPatternRule().getLhs();
            proof = EquivSimplifyingMuProof.create(lhs, true, mu1L, mu2L);

            if (proof == null) {
                return null;
            }

            newpr = Equivalence.create(newpr, proof);
        }

        if (!mu1R.isEmpty()) {
            final PatternTerm rhs = newpr.getPatternRule().getRhs();
            proof = EquivSimplifyingMuProof.create(rhs, false, mu1R, mu2R);

            if (proof == null) {
                return null;
            }

            newpr = Equivalence.create(newpr, proof);
        }

        return newpr;
    }
    
    @Override
    public int getProofStepCount() {
        return 1 + this.parent.getProofStepCount();
    }

    @Override
    public ImmutableList<Pair<Position, Rule>> reconstructSequence() {
        return parent.reconstructSequence();
    }

    /**
     * @return The {@link EquivalenceProof} used to transform.
     */
    public EquivalenceProof getEProof() {
        return this.eProof;
    }

    /**
     * @return If <tt>true</tt>, the lhs was modified, otherwise the rhs.
     */
    public boolean isLHS() {
        return this.eProof.isLHS();
    }

    /**
     * @return The {@link ProofedRule parent} used for tranformation.
     */
    public ProofedRule getParent() {
        return this.parent;
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
        return this.parent.export(eu, indent, addIndent, firstIntermediate, fullProof);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProof(final Export_Util eu) {
        return this.eProof.exportProof(eu);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProofShort(final Export_Util eu) {
        return this.eProof.exportProofShort(eu);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element equivalence = XMLTag.EQUIVALENCE.createElement(doc);
        equivalence.appendChild(this.getPatternRule().toDOM(doc, xmlMetaData));
        equivalence.appendChild(this.parent.toDOM(doc, xmlMetaData));
        if (this.isLHS()) {
            equivalence.appendChild(XMLTag.LEFT.createElement(doc));
        } else {
            equivalence.appendChild(XMLTag.RIGHT.createElement(doc));
        }
        equivalence.appendChild(this.eProof.toDOM(doc, xmlMetaData));
        final Element proofedRule = XMLTag.PROOFED_RULE.createElement(doc);
        proofedRule.appendChild(equivalence);
        return proofedRule;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element equivalence = CPFTag.EQUIVALENCE.createElement(doc);
        equivalence.appendChild(this.parent.toCPF(doc, xmlMetaData));
        if (this.isLHS()) {
            equivalence.appendChild(CPFTag.LEFT.createElement(doc));
        } else {
            equivalence.appendChild(CPFTag.RIGHT.createElement(doc));
        }
        equivalence.appendChild(this.eProof.toCPF(doc, xmlMetaData));
        final Element proofedRule = CPFTag.PATTERN_RULE.createElement(doc);
        proofedRule.appendChild(this.getPatternRule().getLhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(this.getPatternRule().getRhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(equivalence);
        return proofedRule;
    }

}
