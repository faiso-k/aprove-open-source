package aprove.verification.dpframework.Orders.SAT;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class POFormula {

    private Formula<None> formula;
    private Map<Variable<None>, Fact> poConstraints;

    public POFormula(Formula<None> formula, Map<Variable<None>,Fact> poConstraints, FormulaFactory<None> formulaFactory, boolean allowQuasi) {
        this.formula = formula;
        this.poConstraints = poConstraints;
    }

    @Override
    public String toString() {
        return this.formula.toString()+"\n"+this.poConstraints.toString()+"\n"+this.formula.toString(this.poConstraints);
    }

    public Map<Variable<None>, Fact> getPOConstraints() {
        return this.poConstraints;
    }

    public Set<Variable<None>> decode(int[] res, int maxUsedVarId) {
        return POFormula.decode(this.poConstraints, res, maxUsedVarId);
    }

    private static Set<Variable<None>> decode(Map<Variable<None>, Fact> factMap, int[] res, int maxUsedVarId) {
        Set<Integer> isTrue = new LinkedHashSet<Integer>();
        //Set<Integer> isFalse = new LinkedHashSet<Integer>();
        int end = res.length;
        if (maxUsedVarId < res.length) {
            end = maxUsedVarId;
        }
        for (int i = 0; i < end; i++) {
            int value = res[i];
            if (value > 0) {
                isTrue.add(value);
            }/* else {
                isFalse.add(-value);
            }*/
        }
        Set<Variable<None>> knownTrue = new LinkedHashSet<Variable<None>>();
        for (Variable<None> var : factMap.keySet()) {
            if (isTrue.contains(var.getId())) {
                knownTrue.add(var);
            }
        }
        return knownTrue;
    }

    public Formula<None> getFormula() {
        return this.formula;
    }

/*    public static void main(String[] args) {
        POFormula pf = new POFormula(null, null, new VariableFactory());
        List<Formula> cArgs = new ArrayList<Formula>();
        Variable var = pf.varFactory.buildVariable();
        Variable[] vars = new Variable[2];
        vars[0] = pf.varFactory.buildVariable();
        vars[1] = pf.varFactory.buildVariable();
        pf.encodeBot(0,vars , var, cArgs);
        System.out.println(vars);
        System.out.println(var);
        System.out.println(cArgs);
    }*/

}
