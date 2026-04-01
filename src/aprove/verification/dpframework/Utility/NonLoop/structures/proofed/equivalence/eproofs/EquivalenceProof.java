package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.eproofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.xml.*;
import immutables.*;

/**
 * The general class for equivalence proofs of {@link PatternTerm PatternTerms}.
 *
 * @author Tim Enger
 */

public abstract class EquivalenceProof
    implements
        Exportable,
        IExportableProof,
        XMLObligationExportable,
        Immutable,
        CPFAdditional
{

    /**
     * The PatternTerm before it was transformed.
     */
    private final PatternTerm termBefore;

    /**
     * The PatternTterm after it was transformed.
     */
    private final PatternTerm termAfter;

    /**
     * Flag to indicate whether it was the lhs or rhs.
     */
    private final boolean lhs;

    /**
     * Constructor
     *
     * @param tBefore
     *            The {@link PatternTerm} before it was transformed.
     * @param tAfter
     *            The {@link PatternTerm} after it was transformed.
     * @param lhsArg
     *            Flag to indicate whether it was the lhs or rhs. If
     *            <tt>true</tt>, the lhs was modified.
     */
    public EquivalenceProof(final PatternTerm tBefore, final PatternTerm tAfter, final boolean lhsArg) {
        this.lhs = lhsArg;
        this.termBefore = tBefore;
        this.termAfter = tAfter;
    }

    /**
     * @return <tt>True</tt>, if it was the lhs that was modified, otherwise the
     *         rhs.
     */
    public boolean isLHS() {
        return this.lhs;
    }

    /**
     * @return The {@link PatternTerm} <b>before</b> the equivalence
     *         transformation.
     */
    public PatternTerm getTermBefore() {
        return this.termBefore;
    }

    /**
     * @return The {@link PatternTerm} <b>after</b> the equivalence
     *         transformation.
     */
    public PatternTerm getTermAfter() {
        return this.termAfter;
    }

}
