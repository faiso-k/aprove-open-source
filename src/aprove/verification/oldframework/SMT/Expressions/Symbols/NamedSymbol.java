package aprove.verification.oldframework.SMT.Expressions.Symbols;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;

public interface NamedSymbol<RV extends Sort> extends Symbol<RV> {

    String getName();

}
