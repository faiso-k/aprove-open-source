package aprove.input.Programs.prolog.processors.toirswt;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;

class RuleFactory {
    public IGeneralizedRule createUnconditionalRule(TRSFunctionApplication lhs, TRSTerm rhs) {
        final TRSTerm trueTerm = TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE", 0));
        return IGeneralizedRule.create(lhs, rhs, trueTerm);
    }

    public IGeneralizedRule createConditionalRule(TRSFunctionApplication lhs, TRSTerm rhs, TRSTerm condition) {
        return IGeneralizedRule.create(lhs, rhs, condition);
    }
}
