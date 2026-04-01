package aprove.verification.dpframework.Heuristics;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;

/**
 * Condition.<br><br>
 *
 * Created: May 8, 2007<br>
 * Last modified: May 8, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public interface Condition {
    public boolean check(BasicObligation obl, Abortion aborter, RuntimeInformation rti);

    public boolean isApplicable(BasicObligation obl);
}
