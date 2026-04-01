package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * @author christian
 *
 * For easier type checking, edge information which holds information about integers
 * implements this interface
 */
public interface IntegerInformation extends VariableInformation {
    /**
     * @param interestingRefs a list of sets of interesting references
     * @return true if any of the references used in the edge label are interesting
     */
    boolean concernsInterestingRef(Set<AbstractVariableReference>... interestingRefs);

    /**
     * @param varPrefix a String that is prepended to the generated variables'
     *  name.
     * @return an SMTLIB atom corresponding to the encoded integer information.
     */
    SMTLIBTheoryAtom toSMTAtom(String varPrefix);
}
