package aprove.verification.complexity.LowerBounds.BasicStructures;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.Complexity.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;


public class Rule extends AbstractRule {

    private int cost;

    public Rule(TRSFunctionApplication left, TRSTerm right, int cost) {
        super(left, right);
        this.cost = cost;
    }

    public Rule(TRSFunctionApplication left, TRSTerm right) {
        this(left, right, 1);
    }

    @Override
    Rule cloneWith(TRSFunctionApplication newLhs, TRSTerm newRhs) {
        return new Rule(newLhs, newRhs, cost);
    }

    public Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> res = new LinkedHashSet<>();
        res.addAll(this.getLeft().getFunctionSymbols());
        res.addAll(this.getRight().getFunctionSymbols());
        return res;
    }

    @Override
    public String getIndex() {
        return "R";
    }

    @Override
    public Complexity getComplexity() {
        return new PolynomialComplexity(SimplePolynomial.create(cost));
    }

}
