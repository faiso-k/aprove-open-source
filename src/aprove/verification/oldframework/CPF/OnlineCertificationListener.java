package aprove.verification.oldframework.CPF;

import aprove.api.prooftree.*;
import aprove.prooftree.Obligations.*;

public interface OnlineCertificationListener {

    void noteOnlineCertificationResult(CPFCheckResult value, BasicObligationNode obligationNode);

}
