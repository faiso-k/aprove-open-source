package aprove.verification.oldframework.PropositionalLogic;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Interface for MaxSAT engines.
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public interface MaxSATChecker extends SATChecker {

    /**
     * MaxSAT solving for arbitrary propositional formulae.
     * @param formula An unlabelled purely propositional formula
     *  not (necessarily) in CNF
     * @param maxSatFormulas list of some subformulas of <code>formula</code>
     *  such that in addition to having to satisfy <code>formula</code>, the
     *  MaxSATChecker must assign a maximum number of elements of
     *  <code>maxSatFormulas</code> (docu-guess by fuhs)
     * @return An array of ints where -varid denotes false and varid denotes true
     */
    public int[] solve(Formula<None> formula, Collection<Formula<None>> maxSatFormulas, Abortion aborter) throws AbortionException;
}
