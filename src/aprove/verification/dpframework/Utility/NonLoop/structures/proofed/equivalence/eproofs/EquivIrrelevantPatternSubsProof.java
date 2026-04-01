package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.eproofs;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.xml.*;

/**
 * Proof for "Equivalence by Irrelevant Pattern Substitutions"
 *
 * @author Tim Enger
 */

public final class EquivIrrelevantPatternSubsProof extends EquivalenceProof {

    /**
     * The used \sigma'
     */
    private final TRSSubstitution sigmaPrime;

    /**
     * The used \mu'
     */
    private final TRSSubstitution muPrime;

    /**
     * Constructor
     *
     * @param tBefore
     *            The {@link PatternTerm} before it was transformed.
     * @param tAfter
     *            The {@link PatternTerm} after it was transformed.
     * @param lhs
     *            Flag to indicate whether it was the lhs or rhs. If
     *            <tt>true</tt>, the lhs was modified.
     * @param sigmaPrimeArg
     *            The {@link TRSSubstitution sigma'} that was used.
     * @param muPrimeArg
     *            The {@link TRSSubstitution mu'} that was used.
     */
    private EquivIrrelevantPatternSubsProof(final PatternTerm tBefore, final PatternTerm tAfter, final boolean lhs,
            final TRSSubstitution sigmaPrimeArg, final TRSSubstitution muPrimeArg) {
        super(tBefore, tAfter, lhs);
        this.sigmaPrime = sigmaPrimeArg;
        this.muPrime = muPrimeArg;
    }

    /**
     * <p>
     * Factory Method:<br>
     * Equivalence by Irrelevant Pattern Substitutions
     * </p>
     * <p>
     * Let p = t\sigma^n\mu be a pattern term and let \sigma' and \mu' be
     * substitutions such that<br>
     * <br>
     * x\sigma = x\sigma' and x\mu = x\mu' for all x \in rv(p).<br>
     * <br>
     * Then p is equivalent to t\sigma'^n\mu'
     * </p>
     *
     * @param tBefore
     *            The {@link PatternTerm} before it was transformed.
     * @param lhs
     *            Flag to indicate whether it was the lhs or rhs. If
     *            <tt>true</tt>, the lhs was modified.
     * @param sigmaPrime
     *            The {@link TRSSubstitution sigma'} that was used.
     * @param muPrime
     *            The {@link TRSSubstitution mu'} that was used.
     * @return The new {@link EquivIrrelevantPatternSubsProof} if the checks
     *         were successful, <tt>null</tt> otherwise.
     */
    public static EquivIrrelevantPatternSubsProof create(final PatternTerm tBefore,
        final boolean lhs,
        final TRSSubstitution sigmaPrime,
        final TRSSubstitution muPrime) {

        final TRSSubstitution sigma = tBefore.getSigma();
        final TRSSubstitution mu = tBefore.getMu();

        /* check the requirements */
        // x\sigma = x\sigma' and x\mu = x\mu' for all x \in rv(p)
        for (final TRSVariable x : tBefore.getRelevantVariables()) {
            final TRSTerm xSigma = x.applySubstitution(sigma);
            final TRSTerm xSigmaPrime = x.applySubstitution(sigmaPrime);

            if (!xSigma.equals(xSigmaPrime)) {
                if (Globals.DEBUG_NEX) {
                    System.err.println("IrrelevantPatternSubs: tBefore: " + tBefore + " sigma': " + sigmaPrime
                        + " mu': " + muPrime);
                    System.err.println("IrrelevantPatternSubs: xSigma: " + xSigma + " != xSigma': " + xSigmaPrime);
                    System.err.println();
                }
                return null;
            }

            final TRSTerm xMu = x.applySubstitution(mu);
            final TRSTerm xMuPrime = x.applySubstitution(muPrime);

            if (!xMu.equals(xMuPrime)) {
                if (Globals.DEBUG_NEX) {
                    System.err.println("IrrelevantPatternSubs: tBefore: " + tBefore + " sigma': " + sigmaPrime
                        + " mu': " + muPrime);
                    System.err.println("IrrelevantPatternSubs: xMu: " + xMu + " != xMu': " + xMuPrime);
                    System.err.println();
                }
                return null;
            }
        }

        final PatternTerm tAfter = new PatternTerm(tBefore.getT(), sigmaPrime, muPrime);

        // everything was okay, so create the proof.
        return new EquivIrrelevantPatternSubsProof(tBefore, tAfter, lhs, sigmaPrime, muPrime);
    }

    /**
     * @return The used {@link TRSSubstitution sigma'}.
     */
    public TRSSubstitution getSigmaPrime() {
        return this.sigmaPrime;
    }

    /**
     * @return The used {@link TRSSubstitution mu'}.
     */
    public TRSSubstitution getMuPrime() {
        return this.muPrime;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String export(final Export_Util eu) {
        return "Equivalence by Irrelevant Pattern Substitutions " + eu.sigma() + ": " + this.sigmaPrime.export(eu)
            + " " + eu.mu() + ": " + this.muPrime.export(eu);
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
        return "Equiv IPS (" + (this.isLHS() ? "lhs" : "rhs") + ")";
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternEquivalence = XMLTag.PATTERN_EQUIVALENCE.createElement(doc);
        final Element irrelevant = XMLTag.IRRELEVANT.createElement(doc);
        irrelevant.appendChild(this.sigmaPrime.toDOM(doc, xmlMetaData));
        irrelevant.appendChild(this.muPrime.toDOM(doc, xmlMetaData));
        patternEquivalence.appendChild(irrelevant);
        return patternEquivalence;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternEquivalence = CPFTag.PATTERN_EQUIVALENCE.createElement(doc);
        final Element irrelevant = CPFTag.IRRELEVANT.createElement(doc);
        irrelevant.appendChild(this.sigmaPrime.toCPF(doc, xmlMetaData));
        irrelevant.appendChild(this.muPrime.toCPF(doc, xmlMetaData));
        patternEquivalence.appendChild(irrelevant);
        return patternEquivalence;
    }

}
