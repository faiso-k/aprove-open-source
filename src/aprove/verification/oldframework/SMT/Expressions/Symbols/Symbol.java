package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public interface Symbol<RV extends Sort> {
    public Sort[] getArgumentSorts();

    public RV getReturnSort();
}
