package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.eproofs;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.xml.*;

/**
 * Proof for "Equivalence by Domain Renaming".
 *
 * @author Tim Enger
 */

public final class EquivDomainRenamingProof extends EquivalenceProof {

    /**
     * The domain renaming used.
     */
    private final TRSSubstitution dr;

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
     * @param domainRenaming
     *            The {@link TRSSubstitution Domain Renaming} used.
     */
    private EquivDomainRenamingProof(final PatternTerm tBefore, final PatternTerm tAfter, final boolean lhs,
            final TRSSubstitution domainRenaming) {
        super(tBefore, tAfter, lhs);
        this.dr = domainRenaming;
    }

    /**
     * <p>
     * Factory Method:<br>
     * Equivalence by Domain Renaming
     * </p>
     * <p>
     * Let p be a PatternTerm and let \rho be a domain renaming for p. Then p is
     * equivalent to p^\rho.
     * </p>
     *
     * @param tBefore
     *            The {@link PatternTerm} before it was transformed.
     * @param lhs
     *            Flag to indicate whether it was the lhs or rhs. If
     *            <tt>true</tt>, the lhs was modified.
     * @param domainRenaming
     *            The {@link TRSSubstitution Domain Renaming} used.
     * @return The new {@link EquivDomainRenamingProof} if the checks were
     *         successful, <tt>null</tt> otherwise.
     */
    public static EquivDomainRenamingProof create(final PatternTerm tBefore,
        final boolean lhs,
        final TRSSubstitution domainRenaming) {

        /* check requirements */
        // should be a domain renaming
        if (!tBefore.isDomainRenaming(domainRenaming)) {
            return null;
        }

        final PatternTerm tAfter = tBefore.getDomainRenamed(domainRenaming);

        // everything was okay, so create the proof
        return new EquivDomainRenamingProof(tBefore, tAfter, lhs, domainRenaming);
    }

    /**
     * @return The used {@link TRSSubstitution Domain Renaming}
     */
    public TRSSubstitution getDomainRenaming() {
        return this.dr;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String export(final Export_Util eu) {
        return "Equivalence by Domain Renaming of the " + (this.isLHS() ? "lhs" : "rhs") + " with " + this.dr.export(eu);
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
        return "Equiv DR (" + (this.isLHS() ? "lhs" : "rhs") + ")";
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternEquivalence = XMLTag.PATTERN_EQUIVALENCE.createElement(doc);
        final Element domainRenaiming = XMLTag.DOMAIN_RENAIMING.createElement(doc);
        domainRenaiming.appendChild(this.dr.toDOM(doc, xmlMetaData));
        patternEquivalence.appendChild(domainRenaiming);
        return patternEquivalence;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternEquivalence = CPFTag.PATTERN_EQUIVALENCE.createElement(doc);
        final Element domainRenaiming = CPFTag.DOMAIN_RENAIMING.createElement(doc);
        domainRenaiming.appendChild(this.dr.toCPF(doc, xmlMetaData));
        patternEquivalence.appendChild(domainRenaiming);
        return patternEquivalence;
    }

}
