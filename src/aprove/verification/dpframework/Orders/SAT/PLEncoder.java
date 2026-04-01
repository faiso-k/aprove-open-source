package aprove.verification.dpframework.Orders.SAT;


import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;


/**
 *
 * Interface for Propositional Logic encoders.
 *
 */
public interface PLEncoder {

    /**
     *
     * @param poFormula
     *   The PO-Formula to encode to PL.
     * @param aborter
     *   An aborter instance to signal termination.
     *
     */
    public Formula<None> toPropositionalFormula(POFormula poFormula, Abortion aborter) throws AbortionException;

}
