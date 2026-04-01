package aprove.verification.oldframework.PropositionalLogic.TheoryPropositions;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Theory proposition type for purely propositional
 * (i.e., Boolean) formulae. There cannot be any instances
 * of None, so we can only create Boolean variables, but
 * no TheoryPropositions.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public final class None implements TheoryProposition {
    // do not call! there shall be no instances of "None".
    private None() {}
}
