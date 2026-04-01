package aprove.verification.oldframework.CostEquationSystem;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.WeightedIntTrs.*;

public class CostEquation implements AbstractWeightedIntRule<CostEquation> {

    private TRSFunctionApplication left;
    private List<TRSFunctionApplication> right;
    private TRSFunctionApplication condition;
    private SimplePolynomial cost;
    private List<TRSTerm> leftOutputVariables;

    private boolean check() {
        //all lhs args are vars, function symbol is not predefined
        if (ToolBox.PREDEFINED.isPredefined(left.getFunctionSymbol()))
            return false;
        if (!checkArgs(left))
            return false;
        //all rhs args are vars, function symbol is not predefined
        for (TRSFunctionApplication r : right) {
            if (ToolBox.PREDEFINED.isPredefined(r.getFunctionSymbol()))
                return false;
            if (!checkArgs(r))
                return false;
        }
        return true;
    }

    private boolean checkArgs(TRSFunctionApplication fA) {
        for (TRSTerm arg : fA.getArguments())
            if (!checkTerm(arg))
                return false;
        return true;
    }

    private boolean checkTerm(TRSTerm t) {
        if (t.isVariable())
            return true;
        TRSFunctionApplication fA = (TRSFunctionApplication)t;
        if (ToolBox.PREDEFINED.isPredefined(fA.getFunctionSymbol())) {
            return checkArgs(fA);
        } else {
            return false;
        }
    }

    private CostEquation(TRSFunctionApplication left, List<TRSFunctionApplication> right, TRSFunctionApplication condition, SimplePolynomial cost) {
        this.left = left;
        this.right = new ArrayList<>(right);
        this.condition = condition;
        this.cost = cost;
        assert check();
    }

    private CostEquation(TRSFunctionApplication left, List<TRSFunctionApplication> right, TRSFunctionApplication condition, SimplePolynomial cost, List<TRSTerm> leftOutputVariables) {
        this.left = left;
        this.right = new ArrayList<>(right);
        this.condition = condition;
        this.cost = cost;
        this.leftOutputVariables = leftOutputVariables;
        assert check();
    }

    public static CostEquation create(TRSFunctionApplication left, List<TRSFunctionApplication> right, TRSFunctionApplication condition, SimplePolynomial cost) {
        return new CostEquation(left, right, condition, cost);
    }

    public static CostEquation create(TRSFunctionApplication left, List<TRSFunctionApplication> right, TRSFunctionApplication condition, SimplePolynomial cost, List<TRSTerm> leftOutputVariables) {
        return new CostEquation(left, right, condition, cost, leftOutputVariables);
    }

    public static CostEquation create(TRSFunctionApplication left, TRSFunctionApplication right,  TRSFunctionApplication condition, SimplePolynomial cost) {
        return new CostEquation(left, Collections.singletonList(right), condition, cost);
    }

    public static CostEquation create(TRSFunctionApplication left, TRSFunctionApplication right,  TRSFunctionApplication condition, SimplePolynomial cost, List<TRSTerm> leftOutputVariables) {
        return new CostEquation(left, Collections.singletonList(right), condition, cost, leftOutputVariables);
    }

    @Override
    public CostEquation copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, TRSFunctionApplication newCond,
            SimplePolynomial newUpperBound, SimplePolynomial newLowerBound) {
        return create(newLeft, newRight, newCond, newUpperBound);
    }

    @Override
    public CostEquation copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, TRSFunctionApplication newCond,
                             SimplePolynomial newUpperBound, SimplePolynomial newLowerBound, List<TRSTerm> newOutputVariable) {
        return create(newLeft, newRight, newCond, newUpperBound, newOutputVariable);
    }

    @Override
    public TRSFunctionApplication getLeft() {
        return left;
    }

    @Override
    public List<TRSFunctionApplication> getRight() {
        return right;
    }

    @Override
    public TRSFunctionApplication getCondition() {
        return condition;
    }

    @Override
    public SimplePolynomial getUpperBound() {
        return cost;
    }

    @Override
    public Optional<SimplePolynomial> getLowerBound() {
        return Optional.empty();
    }

    @Override
    public List<TRSTerm> getLeftOutputVariables() { return leftOutputVariables; }

    @Override
    public CostEquation getWithRenamedVariables(Map<TRSVariable, TRSVariable> renamingMap) {
        TRSFunctionApplication newLeft = left.renameVariables(renamingMap);
        List<TRSFunctionApplication> newRight = new ArrayList<>(right.size());
        for (TRSFunctionApplication r : right) {
            newRight.add(r.renameVariables(renamingMap));
        }
        TRSFunctionApplication newCondition = condition.renameVariables(renamingMap);
        Map<String, String> stringMap = new LinkedHashMap<>();
        for (Entry<TRSVariable, TRSVariable> e: renamingMap.entrySet()) {
            stringMap.put(e.getKey().toString(), e.getValue().toString());
        }
        SimplePolynomial newCost = cost.replace(stringMap);
        // rename leftOutputVariables
        List<TRSTerm> newOutputVariables = new ArrayList<>();
        for (TRSTerm term : leftOutputVariables) {
            if (renamingMap.containsKey(term)) {
                newOutputVariables.add(renamingMap.get(term));
            }
        }
        return create(newLeft, newRight, newCondition, newCost, newOutputVariables);
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        sb.append(left.export(eu)).append(" = ");
        sb.append(cost);
        for (TRSFunctionApplication r : right) {
            sb.append(" + ").append(r.export(eu));
        }
        sb.append(" :|: ").append(WeightedRule.exportExp(eu, condition));
        return sb.toString();
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((condition == null) ? 0 : condition.hashCode());
        result = prime * result + ((cost == null) ? 0 : cost.hashCode());
        result = prime * result + ((left == null) ? 0 : left.hashCode());
        result = prime * result + ((right == null) ? 0 : right.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        CostEquation other = (CostEquation) obj;
        if (condition == null) {
            if (other.condition != null)
                return false;
        } else if (!condition.equals(other.condition))
            return false;
        if (cost == null) {
            if (other.cost != null)
                return false;
        } else if (!cost.equals(other.cost))
            return false;
        if (left == null) {
            if (other.left != null)
                return false;
        } else if (!left.equals(other.left))
            return false;
        if (right == null) {
            if (other.right != null)
                return false;
        } else if (!right.equals(other.right))
            return false;
        return true;
    }
}
