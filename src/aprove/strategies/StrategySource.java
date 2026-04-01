/*
 * Created on Jan 8, 2005
 */
package aprove.strategies;

import aprove.strategies.Parameters.*;
import aprove.verification.oldframework.Input.*;


/**
 * @author rabe
 */
public interface StrategySource {

    public StrategyProgram getStrategyProgram(AnnotatedInput annotatedInput);

}
