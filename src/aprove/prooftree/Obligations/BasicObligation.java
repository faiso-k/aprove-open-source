package aprove.prooftree.Obligations;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.xml.*;
import immutables.*;

/**
 * A basic obligation.
 * @author unknown
 * @version $Id$
 */
public interface BasicObligation extends Immutable, Exportable, XMLObligationExportable, CPFInputProblem {

    /**
     * @return the name of the sub strategy in current.strategy which should be used for this obligation
     */
    String getStrategyName();

    /**
     * The default implementation in DefaultBasicObligation returns false. This method should be overridden by
     * obligations offering certifiable techniques to return true in this case.
     * @return True iff there are some certifiable techniques which can be applied to this obligation. False otherwise.
     */
    boolean offersCertifiableTechniques();

    /**
     * @return a deep copy of itself.
     */
    BasicObligation deepcopy();

    /**
     * @return some unique string identifying this obligation.
     */
    String getId();

    /**
     * @param length specifies if a short or long name is requested.
     * @return a short ("QDP", "QTRS") or long name for this obligation.
     */
    String getName(NameLength length);

    /**
     * @return The type of obligation we are at.
     */
    ObligationType getObligationType();

    /**
     *
     * @return The direct parent obligation.
     */
    BasicObligation getParent();

    /**
     * @return The proof result which is used as introduction
     *         ("This obligation ... could be proven/disproven/not proven") by the non-GUI proof output.
     *         This does /not/ contain the proof tree, but just the overall result.
     */
    ProofPurposeDescriptor getProofPurposeDescriptor();

    /**
     * @return truth value known for this obligation.
     */
    TruthValue getTruthValue();

    /**
     * @return a more or less deep copy of itself, if it is needed.
     *  Returns this if no copy is needed.
     */
    BasicObligation maybeCopy();

    /**
     * @param truth the truth value of this obligation.
     */
    void setTruth(TruthValue truth);

    /**
     * Obligation types.
     * @author unknown
     * @version $Id$
     */
    enum ObligationType {

        /**
         * Dependency pair obligation.
         */
        DP,

        /**
         * TODO Docu guess: Relative obligation.
         */
        RELATIVE,

        /**
         * TRS obligation.
         */
        TRS,

        /**
         * Unknown obligation type.
         */
        UNKNOWN

    }

}
