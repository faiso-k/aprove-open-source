package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * <p>
 * <b>Expand Sigma</b>
 * </p>
 * <p>
 * PatternTerm: t\sigma^n\mu<br>
 * <br>
 * Applies \sigma k-times to t.
 * </p>
 * <p>
 * At the moment we need this functionality to show nontermination of the
 * following examples:
 * <ul>
 * <li>nonloop/TRS/emmes/ex7_2.trs</li>
 * <li>nonloop/TRS/emmes/ex7_4.trs</li>
 * <li>nonloop/TRS/emmes/ex7_7.trs</li>
 * <li>nonloop/TRS/emmes/ex7_9.trs</li>
 * </ul>
 * </p>
 *
 * @author Tim Enger
 */
public final class ExpandSigma extends ProofedRule {

    /**
     * k!
     */
    private final int k;

    /**
     * The parent used for expansion.
     */
    private final ProofedRule parent;

    /**
     * Constructor
     *
     * @param lhs
     *            The {@link PatternTerm left-hand side}
     * @param rhs
     *            The {@link PatternTerm left-hand side}
     * @param parentArg
     *            The {@link ProofedRule parent} of the new lhs and rhs.
     * @param kArg
     *            The number of applications of {@link TRSSubstitution \sigma}.
     */
    private ExpandSigma(final PatternTerm lhs, final PatternTerm rhs, final ProofedRule parentArg, final int kArg) {
        super(lhs, rhs, parentArg.getR(), parentArg.getP(), parentArg.hasPStep());
        this.k = kArg;
        this.parent = parentArg;
    }

    /**
     * Factory method for "Expand Sigma".
     *
     * @param lr
     *            The {@link ProofedRule} to apply to
     * @param k
     *            The number of applications of {@link TRSSubstitution \sigma}.
     * @return The new {@link ProofedRule}.
     */
    public static ProofedRule create(final ProofedRule lr, final int k) {

        if (k < 0) {
            return null;
        }

        if (k == 0) {
            return lr;
        }

        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm l = pRule.getLhs();
        final PatternTerm r = pRule.getRhs();

        TRSTerm lBase = l.getT();
        final TRSSubstitution lSigma = l.getSigma();
        TRSTerm rBase = r.getT();
        final TRSSubstitution rSigma = r.getSigma();

        for (int i = 0; i < k; ++i) {
            lBase = lBase.applySubstitution(lSigma);
            rBase = rBase.applySubstitution(rSigma);
        }

        if (lBase.equals(l.getT()) && rBase.equals(r.getT())) {
            return lr;
        }

        return new ExpandSigma(new PatternTerm(lBase, lSigma, l.getMu()), new PatternTerm(rBase, rSigma, r.getMu()),
            lr, k);
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
     * {@inheritDoc}
     */
    @Override
    public String exportProof(final Export_Util eu) {
        return "Expand Sigma " + this.k + " times";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProofShort(final Export_Util eu) {
        return "Expand Sigma";
    }

    /**
     * @return The {@link ProofedRule parent} used for expansion.
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

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        throw new UnsupportedOperationException("ExpandSigma not certifiable.");
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element instantiation =
            CPFTag.INSTANTIATION_PUMPING.create(
                doc,
                this.parent.toCPF(doc, xmlMetaData),
                CPFTag.POWER.create(doc, doc.createTextNode(this.k + "")));
        return CPFTag.PATTERN_RULE.create(doc, this.getPatternRule().getLhs().toCPF(doc, xmlMetaData), this
            .getPatternRule()
            .getRhs()
            .toCPF(doc, xmlMetaData), instantiation);
    }

}
