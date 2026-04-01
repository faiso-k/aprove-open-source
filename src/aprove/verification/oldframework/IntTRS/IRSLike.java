package aprove.verification.oldframework.IntTRS;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;

public interface IRSLike extends BasicObligation {

    Set<IGeneralizedRule> getRules();
    TRSFunctionApplication getStartTerm();
    IRSLike create(Set<IGeneralizedRule> rules, TRSFunctionApplication startTerm);
    boolean isBounded();

}
