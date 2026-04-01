package aprove.verification.dpframework.BasicStructures;

import java.util.*;

/**
 * Objects containing rules can return the set of all rules.
 */
public interface HasRules<R extends HasRuleForm> {

    Set<R> getRules();

}
