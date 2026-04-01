package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.eproofs;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.xml.*;

/**
 * Proof for "Equivalence by Simplifying Mu"
 *
 * @author Tim Enger
 */

public final class EquivSimplifyingMuProof extends EquivalenceProof {

    /**
     * The mu part to apply to t
     */
    private final TRSSubstitution mu1;

    /**
     * The mu part to be kept
     */
    private final TRSSubstitution mu2;

    /**
     * Constructor
     *
     * @param tBefore
     *            The {@link PatternTerm} before it was transformed.
     * @param tAfter
     *            The {@link PatternTerm} after transformation.
     * @param lhs
     *            Flag to indicate whether it was the lhs or rhs. If
     *            <tt>true</tt>, the lhs was modified.
     * @param mu1Arg
     *            The {@link TRSSubstitution mu}-part to apply to t.
     * @param mu2Arg
     *            The {@link TRSSubstitution mu}-part to be kept.
     */
    private EquivSimplifyingMuProof(final PatternTerm tBefore, final PatternTerm tAfter, final boolean lhs,
            final TRSSubstitution mu1Arg, final TRSSubstitution mu2Arg) {
        super(tBefore, tAfter, lhs);
        this.mu1 = mu1Arg;
        this.mu2 = mu2Arg;
    }

    /**
     * <p>
     * Factory Method:<br>
     * Equivalence by Simplifying mu
     * </p>
     * <p>
     * Let p = t\sigma^n\mu be a pattern term and let \mu = \mu_1\mu_2 where
     * \mu_1 commutes with \sigma.<br>
     * <br>
     * Then p is equivalent to (t\mu_1)\sigma'^n\mu_2
     * </p>
     *
     * @param tBefore
     *            The {@link PatternTerm} before it was transformed.
     * @param lhs
     *            Flag to indicate whether it was the lhs or rhs. If
     *            <tt>true</tt>, the lhs was modified.
     * @param mu1
     *            The {@link TRSSubstitution mu}-part to apply to t.
     * @param mu2
     *            The {@link TRSSubstitution mu}-part to be kept.
     * @return The new {@link EquivIrrelevantPatternSubsProof} if the checks
     *         were successful, <tt>null</tt> otherwise.
     */
    public static EquivSimplifyingMuProof create(final PatternTerm tBefore,
        final boolean lhs,
        final TRSSubstitution mu1,
        final TRSSubstitution mu2) {

        final TRSSubstitution mu = tBefore.getMu();
        final TRSSubstitution sigma = tBefore.getSigma();

        // mu = mu1 mu2
        if (!mu1.compose(mu2).equals(mu)) {
            return null;
        }

        // mu1 and sigma commute
        if (!Utils.commutative(mu1, sigma)) {
            return null;
        }

        final PatternTerm tAfter = new PatternTerm(tBefore.getT().applySubstitution(mu1), sigma, mu2);

        return new EquivSimplifyingMuProof(tBefore, tAfter, lhs, mu1, mu2);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String export(final Export_Util eu) {
        return "Equivalency by Simplifying Mu with " + eu.mu() + "1: " + this.mu1.export(eu) + " " + eu.mu() + "2: "
            + this.mu2.export(eu);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProof(final Export_Util eu) {
        return this.export(eu);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProofShort(final Export_Util eu) {
        return "Equiv S" + eu.mu() + " (" + (this.isLHS() ? "lhs" : "rhs") + ")";
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternEquivalence = XMLTag.PATTERN_EQUIVALENCE.createElement(doc);
        final Element simplification = XMLTag.SIMPLIFICATION.createElement(doc);
        simplification.appendChild(this.mu1.toDOM(doc, xmlMetaData));
        simplification.appendChild(this.mu2.toDOM(doc, xmlMetaData));
        patternEquivalence.appendChild(simplification);
        return patternEquivalence;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternEquivalence = CPFTag.PATTERN_EQUIVALENCE.createElement(doc);
        final Element simplification = CPFTag.SIMPLIFICATION.createElement(doc);
        simplification.appendChild(this.mu1.toCPF(doc, xmlMetaData));
        simplification.appendChild(this.mu2.toCPF(doc, xmlMetaData));
        patternEquivalence.appendChild(simplification);
        return patternEquivalence;
    }

}
