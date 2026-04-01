package aprove.verification.probabilistic.BasicStructures;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Objects that have the form of a probabilistic rewrite rule l -> {p1:t1, ..., pk:tk}.
 *
 * @author Jan-Christoph Kassing
 * @version $Id$
 */
public interface HasProbRuleForm extends HasLHS, HasProbRHS, HasFunctionSymbols {

}
