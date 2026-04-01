package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class LcmAndBGetter implements LinearFormulaVisitor<Object>{

    protected AlgebraVariable variable;

    protected ArrayList<LinearConstraint> b;

    protected ArrayList<Integer> lcm;

    private LcmAndBGetter(AlgebraVariable variable){
        this.variable = variable;

        this.b = new ArrayList<LinearConstraint>();
        this.lcm = new ArrayList<Integer>();
    }

    public static Pair<Integer, List<LinearConstraint>> apply(AlgebraVariable var, LinearFormula linearFormula){
        LcmAndBGetter lcmAndBGetter = new LcmAndBGetter(var);
        linearFormula.apply(lcmAndBGetter);

        int l = 1;

        for(int i = 0; i < lcmAndBGetter.lcm.size(); i++){
            l = Rational.lcm(l, lcmAndBGetter.lcm.get(i));
        }

        Pair<Integer, List<LinearConstraint>> p =
            new Pair<Integer, List<LinearConstraint>>(l, lcmAndBGetter.b);
        return p;

    }

    @Override
    public Object caseAllQuantifiedLinearFormula(AllQuantifiedLinearFormula allLinearFormula) {

        System.err.println("May not occur");
        return null;
    }

    @Override
    public Object caseAnd(AndLinearFormula and) {

        and.getLeft().apply(this);
        and.getRight().apply(this);

        return null;
    }

    @Override
    public Object caseExistentialQuantifiedLinearFormula(ExistentialQuantifiedLinearFormula existentialLinearFormula) {

        System.err.println("May not occur");
        return null;
    }

    @Override
    public Object caseLinearConstraint(LinearConstraint linearConstraint) {
        Map<AlgebraVariable, Rational> coeffs = linearConstraint.getCoefficients();

        Rational value = coeffs.get(this.variable);

        if(value == null){
            return null;
        }
        else{
            int intvalue = value.getNumerator();
            if(intvalue > 0){
                // type A
                return null;
            }
            else{
                // type B
                this.b.add(linearConstraint.deepcopy());
                this.lcm.add(-intvalue);

                return null;
            }
        }
    }

    @Override
    public Object caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {

        // type D

        int m = moduloLinearFormula.getModulo();
        this.lcm.add(m);

        return null;
    }

    @Override
    public Object caseNot(NotLinearFormula not) {
        not.getSubFormula().apply(this);
        return null;
    }

    @Override
    public Object caseOr(OrLinearFormula or) {
        or.getLeft().apply(this);
        or.getRight().apply(this);

        return null;
    }

    @Override
    public Object caseTruthValue(TruthValueLinearFormula truthvalue) {
        return null;
    }

}
