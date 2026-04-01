package aprove.verification.dpframework.IDPProblem.Processors.algorithms.orders;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.*;

public interface IActiveOrder extends ExportableOrder<TRSTerm> {


    public boolean orientsStrictly(GeneralizedRule rule) throws AbortionException;
    public Map<GeneralizedRule, Map<RelDependency, IDirection>> getOrientedUsables();

}
