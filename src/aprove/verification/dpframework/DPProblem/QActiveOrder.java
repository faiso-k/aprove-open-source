package aprove.verification.dpframework.DPProblem;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;

public interface QActiveOrder extends ExportableOrder<TRSTerm> {

    public boolean checkQActiveCondition(QActiveCondition condition);

}
