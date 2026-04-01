package aprove.verification.oldframework.WeightedIntTrs;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;

public class WeightedRule implements AbstractWeightedIntRule<WeightedRule> {

    private IGeneralizedRule rule;
    private SimplePolynomial lowerBound;
    private SimplePolynomial upperBound;
    private List<TRSTerm> leftOutputVariable = new ArrayList<>();

    public WeightedRule(IGeneralizedRule rule, SimplePolynomial lowerBound, SimplePolynomial upperBound) {
        assert rule.getRight() instanceof TRSFunctionApplication;
        assert rule.getCondTerm() instanceof TRSFunctionApplication;
        this.rule = rule;
        this.upperBound = upperBound;
        this.lowerBound = lowerBound;
    }

    public WeightedRule(TRSFunctionApplication lhs, TRSFunctionApplication rhs, TRSFunctionApplication cond, SimplePolynomial lowerBound, SimplePolynomial upperBound) {
        this(IGeneralizedRule.create(lhs, rhs, cond), lowerBound, upperBound);
    }

    @Override
    public WeightedRule copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, TRSFunctionApplication newCond,
            SimplePolynomial newUpperBound, SimplePolynomial newLowerBound) {
        assert newRight.size() == 1;
        return new WeightedRule(newLeft, newRight.iterator().next(), newCond, newLowerBound, newUpperBound);
    }

    @Override
    public WeightedRule copy(TRSFunctionApplication newLeft, List<TRSFunctionApplication> newRight, TRSFunctionApplication newCond,
                             SimplePolynomial newUpperBound, SimplePolynomial newLowerBound, List<TRSTerm> leftOutputVariable) {
        assert newRight.size() == 1;
        return new WeightedRule(newLeft, newRight.iterator().next(), newCond, newLowerBound, newUpperBound);
    }

    public IGeneralizedRule getRule() {
        return rule;
    }

    @Override
    public SimplePolynomial getUpperBound() {
        return upperBound;
    }

    @Override
    public Optional<SimplePolynomial> getLowerBound() {
        return Optional.of(lowerBound);
    }

    @Override
    public List<TRSTerm> getLeftOutputVariables() { return leftOutputVariable; }

    @Override
    public String export(Export_Util eu) {
        String left = getLeft().export(eu);
        String arrowWithCosts = eu.escape("-{")
                + lowerBound.export(eu)
                + eu.export(",")
                + upperBound.export(eu)
                + eu.escape("}>");
        String right = exportExp(eu, getR());
        String cond = exportExp(eu, getCondition());
        return left + " " + arrowWithCosts + " " + right + " :|: " + cond;
    }

    private static String exportFunctionApplication(Export_Util eu, TRSFunctionApplication fA) {
        String res = fA.getRootSymbol().export(eu) + eu.escape("(");
        List<TRSTerm> args = fA.getArguments();
        for (int i = 0; i < args.size(); i++) {
            if (i > 0) {
                res += eu.escape(", ");
            }
            TRSTerm arg = args.get(i);
            res += exportExp(eu, arg);
        }
        res += eu.export(")");
        return res;
    }

    public static String exportExp(Export_Util eu, TRSTerm cond) {
        if (cond.equals(ToolBox.buildTrue())) {
            return "0 >= 0";
        } else if (cond.isVariable() || cond.isConstant()) {
            return cond.export(eu);
        }
        TRSFunctionApplication fun = (TRSFunctionApplication) cond;
        FunctionSymbol f = fun.getRootSymbol();
        if (f.equals(Func.Land.asFunctionSymbol())) {
            return exportExp(eu, fun.getArgument(0)) + " && " + exportExp(eu, fun.getArgument(1));
        } else if (f.equals(Func.Lnot.asFunctionSymbol())) {
            return "!(" + exportExp(eu, fun.getArgument(0)) + ")";
        } else if (f.equals(Func.Add.asFunctionSymbol())) {
            return exportExp(eu, fun.getArgument(0)) + " + " + exportExp(eu, fun.getArgument(1));
        } else if (f.equals(Func.Sub.asFunctionSymbol())) {
            return exportExp(eu, fun.getArgument(0)) + " - " + exportExp(eu, fun.getArgument(1));
        } else if (f.equals(Func.Mul.asFunctionSymbol())) {
            return exportExp(eu, fun.getArgument(0)) + " * " + exportExp(eu, fun.getArgument(1));
        } else if (f.equals(Func.Div.asFunctionSymbol())) {
            return exportExp(eu, fun.getArgument(0)) + " / " + exportExp(eu, fun.getArgument(1));
        } else if (f.equals(Func.Mod.asFunctionSymbol())) {
            return exportExp(eu, fun.getArgument(0)) + " % " + exportExp(eu, fun.getArgument(1));
        } else if (f.getArity() == 2) {
            TRSTerm arg1 = fun.getArgument(0);
            TRSTerm arg2 = fun.getArgument(1);
            if (f.equals(Func.Le.asFunctionSymbol())) {
                return exportExp(eu, arg1) + " <= " + exportExp(eu, arg2);
            } else if (f.equals(Func.Lt.asFunctionSymbol())) {
                return exportExp(eu, arg1) + " < " + exportExp(eu, arg2);
            } else if (f.equals(Func.Ge.asFunctionSymbol())) {
                return exportExp(eu, arg1) + " >= " + exportExp(eu, arg2);
            } else if (f.equals(Func.Gt.asFunctionSymbol())) {
                return exportExp(eu, arg1) + " > " + exportExp(eu, arg2);
            } else if (f.equals(Func.Eq.asFunctionSymbol())) {
                return exportExp(eu, arg1) + " = " + exportExp(eu, arg2);
            } else if (f.equals(Func.Neq.asFunctionSymbol())) {
                return exportExp(eu, arg1) + " != " + exportExp(eu, arg2);
            }
        } else if (f.equals(Func.UnaryMinus.asFunctionSymbol())) {
            return "-" + exportExp(eu, fun.getArgument(0));
        }
        return exportFunctionApplication(eu, fun);
    }

    public TRSFunctionApplication getR() {
        return (TRSFunctionApplication) rule.getRight();
    }

    @Override
    public List<TRSFunctionApplication> getRight() {
        return Collections.singletonList(getR());
    }

    @Override
    public TRSFunctionApplication getLeft() {
        return rule.getLeft();
    }

    @Override
    public TRSFunctionApplication getCondition() {
        return (TRSFunctionApplication) rule.getCondTerm();
    }

    @Override
    public WeightedRule getWithRenamedVariables(Map<TRSVariable, TRSVariable> renamingMap) {
        IGeneralizedRule newRule = rule.getWithRenamedVariables(renamingMap);
        Map<String, String> stringMap = new LinkedHashMap<>();
        for (Entry<TRSVariable, TRSVariable> e: renamingMap.entrySet()) {
            stringMap.put(e.getKey().toString(), e.getValue().toString());
        }
        SimplePolynomial newUpperBound = upperBound.replace(stringMap);
        SimplePolynomial newLowerBound = lowerBound.replace(stringMap);
        return new WeightedRule(newRule, newLowerBound, newUpperBound);
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((lowerBound == null) ? 0 : lowerBound.hashCode());
        result = prime * result + ((rule == null) ? 0 : rule.hashCode());
        result = prime * result + ((upperBound == null) ? 0 : upperBound.hashCode());
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
        WeightedRule other = (WeightedRule) obj;
        if (lowerBound == null) {
            if (other.lowerBound != null)
                return false;
        } else if (!lowerBound.equals(other.lowerBound))
            return false;
        if (rule == null) {
            if (other.rule != null)
                return false;
        } else if (!rule.equals(other.rule))
            return false;
        if (upperBound == null) {
            if (other.upperBound != null)
                return false;
        } else if (!upperBound.equals(other.upperBound))
            return false;
        return true;
    }
}
