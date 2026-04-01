package aprove.verification.oldframework.WeightedIntTrs;

import static aprove.verification.oldframework.Utility.Collection_Util.*;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

public interface AbstractWeightedIntRule<T extends AbstractWeightedIntRule<T>> extends Exportable {

    public default T copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight) {
        return copy(newLeft, newRight, getCondition());
    }

    public default T copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, List<TRSTerm> newLeftOutputVariables) {
        return copy(newLeft, newRight, getCondition(), newLeftOutputVariables);
    }

    public default T copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, TRSFunctionApplication newCond) {
        return copy(newLeft, newRight, newCond, getUpperBound(), getLowerBound().orElse(null));
    }

    public default T copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, TRSFunctionApplication newCond, List<TRSTerm> leftOutputVariables) {
        return copy(newLeft, newRight, newCond, getUpperBound(), getLowerBound().orElse(null), leftOutputVariables);
    }

    public T copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, TRSFunctionApplication newCond,
            SimplePolynomial newUpperBound, SimplePolynomial newLowerBound);

    public T copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, TRSFunctionApplication newCond,
                  SimplePolynomial newUpperBound, SimplePolynomial newLowerBound, List<TRSTerm> leftOutputVariables);

    public T getWithRenamedVariables(Map<TRSVariable, TRSVariable> renamingMap);

    public TRSFunctionApplication getLeft();

    public List<TRSFunctionApplication> getRight();

    public TRSFunctionApplication getCondition();

    public SimplePolynomial getUpperBound();

    public Optional<SimplePolynomial> getLowerBound();

    public List<TRSTerm> getLeftOutputVariables();

    public default FunctionSymbol getRootSymbol() {
        return getLeft().getRootSymbol();
    }

    public default Set<TRSFunctionApplication> getTerms() {
        Set<TRSFunctionApplication> res = new HashSet<>();
        res.add(getLeft());
        res.addAll(getRight());
        return res;
    }

    public default Set<TRSVariable> getVariables() {
        Set<TRSVariable> res = new HashSet<>();
        res.addAll(getLeft().getVariables());
        for (TRSFunctionApplication r : getRight()) {
            res.addAll(r.getVariables());
        }
        res.addAll(getCondition().getVariables());
        return res;
    }

    public default Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> res = new HashSet<>();
        res.add(getLeft().getFunctionSymbol());
        for (TRSFunctionApplication r : getRight()) {
            res.add(r.getFunctionSymbol());
        }
        return res;
    }

    public default Set<HasName> getUsedNames() {
        return union(getVariables(), getFunctionSymbols());
    }
}
