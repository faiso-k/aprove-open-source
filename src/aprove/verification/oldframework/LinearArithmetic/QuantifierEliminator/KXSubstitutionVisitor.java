package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class KXSubstitutionVisitor implements LinearFormulaVisitor<LinearFormula>{

    protected int k;

    protected AlgebraVariable x;

    protected Map<AlgebraVariable, Integer> t;

    protected int cpj;

    public KXSubstitutionVisitor(int k, AlgebraVariable x, Map<AlgebraVariable, Integer> t, int cpj){
        this.k = k;
        this.x = x;
        this.t = t;
        this.cpj = cpj;
    }

    @Override
    public LinearFormula caseAllQuantifiedLinearFormula(AllQuantifiedLinearFormula allLinearFormula) {

        System.err.println("May not occur");
        return null;
    }

    @Override
    public LinearFormula caseAnd(AndLinearFormula and) {

        LinearFormula left = and.getLeft().apply(this);
        LinearFormula right = and.getRight().apply(this);

        return new AndLinearFormula(left, right);
    }

    @Override
    public LinearFormula caseExistentialQuantifiedLinearFormula(ExistentialQuantifiedLinearFormula existentialLinearFormula) {

        System.err.println("May not occur");
        return null;
    }

    @Override
    public LinearFormula caseLinearConstraint(LinearConstraint linearConstraint) {

        Map<AlgebraVariable, Rational> tprime = linearConstraint.getCoefficients();
        Rational kprimeRational = tprime.remove(this.x);

        Map<AlgebraVariable, Integer> tcopy = new HashMap<AlgebraVariable, Integer>(this.t.size());
        for (Entry<AlgebraVariable, Integer> entry : this.t.entrySet()) {
            tcopy.put((AlgebraVariable)entry.getKey().deepcopy(), entry.getValue().intValue());
        }


        if(kprimeRational == null){
            // nothing to do
            return linearConstraint.deepcopy();
        }
        else{
            int kprime = kprimeRational.getNumerator();

            if(kprime > 0){
                // type A

                int cprime = linearConstraint.getConstant().getNumerator();

                int newConstant = this.k*cprime - kprime*this.cpj;

                Map<AlgebraVariable, Rational> newCoeffs = new HashMap<AlgebraVariable, Rational>();

                // subtract the common variable and add the variables only in t
                for (Entry<AlgebraVariable, Integer> entry : tcopy.entrySet()) {
                    AlgebraVariable var = entry.getKey();
                    Integer t_var = entry.getValue();

                    Rational tprime_var = tprime.remove(var);

                    if(tprime_var == null){
                        tprime_var = new Rational(0);
                    }

                    tprime_var = tprime_var.negate();

                    Rational newCoeff = kprimeRational.times(new Rational(t_var)).minus(
                            (new Rational(this.k)).times(tprime_var)) ;

                    if(! newCoeff.equals(Rational.zero)){
                        newCoeffs.put(var, newCoeff);
                    }
                }
                // subtract the rest
                for (Entry<AlgebraVariable, Rational> entry : tprime.entrySet()) {
                    AlgebraVariable var = entry.getKey();
                    Rational tprime_var = entry.getValue().negate();

                    Rational newCoeff = tprime_var.times(new Rational(-this.k));

                    newCoeffs.put(var, newCoeff);
                }

                LinearConstraint res = new LinearConstraint(newCoeffs, ConstraintType.LESS, new Rational(newConstant));

                return res;
            }
            else{
                // type B

                kprimeRational = kprimeRational.negate();
                kprime = -kprime;

                int cprime = - linearConstraint.getConstant().getNumerator();

                int newConstant = kprime*this.cpj - this.k*cprime;

                Map<AlgebraVariable, Rational> newCoeffs = new HashMap<AlgebraVariable, Rational>();

                // subtract the common variable and add the variables only in tprime
                for (Entry<AlgebraVariable, Rational> entry : tprime.entrySet()) {
                    AlgebraVariable var = entry.getKey();
                    Rational tprime_var = entry.getValue();

                    Integer t_var = tcopy.remove(var);

                    if(t_var == null){
                        t_var = 0;
                    }

//                    tprime_var = 0;

                    Rational newCoeff = (new Rational(this.k)).times(tprime_var).   minus(
                            kprimeRational.times(new Rational(t_var)));

                    if(! newCoeff.equals(Rational.zero)){
                        newCoeffs.put(var, newCoeff);
                    }
                }
                // subtract the rest
                for (Entry<AlgebraVariable, Integer> entry : tcopy.entrySet()) {
                    AlgebraVariable var = entry.getKey();
                    Integer t_var = entry.getValue();

                    Rational newCoeff = (new Rational(-t_var)).times(kprimeRational);

                    newCoeffs.put(var, newCoeff);
                }

                LinearConstraint res = new LinearConstraint(newCoeffs, ConstraintType.LESS, new Rational(newConstant));

                return res;
            }

        }
    }

    @Override
    public LinearFormula caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {
        Map<AlgebraVariable, Integer> tprime = moduloLinearFormula.getCoefficients();
        Integer kprime = tprime.remove(this.x);

        if(kprime == null){
            // nothing to do
            return moduloLinearFormula.deepcopy();
        }
        else{
            // type C

            int modulo = moduloLinearFormula.getModulo();
            int newModulo = this.k*modulo;

            int cprime = moduloLinearFormula.getConstant();
            int newConstant = this.k*cprime + kprime*this.cpj;

            Map<AlgebraVariable, Integer> newCoeffs = new HashMap<AlgebraVariable, Integer>();

            // add the common variable and add the variables only in t
            for (Entry<AlgebraVariable, Integer> entry : this.t.entrySet()) {
                AlgebraVariable var = entry.getKey();
                Integer t_var = entry.getValue();

                Integer tprime_var = tprime.remove(var);

                if(tprime_var == null){
                    tprime_var = 0;
                }

                int newCoeff = this.k * tprime_var + kprime * t_var;

                if(newCoeff!=0){
                    newCoeffs.put(var, newCoeff);
                }
            }
            // add the rest
            for (Entry<AlgebraVariable, Integer> entry : tprime.entrySet()) {
                AlgebraVariable var = entry.getKey();
                Integer tprime_var = entry.getValue();

                newCoeffs.put(var, this.k*tprime_var);
            }

            return new ModuloLinearFormula(newModulo, newCoeffs, newConstant);
        }
    }

    @Override
    public LinearFormula caseNot(NotLinearFormula not) {
        LinearFormula subformula = not.getSubFormula().apply(this);
        return new NotLinearFormula(subformula);
    }

    @Override
    public LinearFormula caseOr(OrLinearFormula or) {
        LinearFormula left = or.getLeft().apply(this);
        LinearFormula right = or.getRight().apply(this);

        return new OrLinearFormula(left, right);
    }

    @Override
    public LinearFormula caseTruthValue(TruthValueLinearFormula truthvalue) {
        return truthvalue.deepcopy();
    }

}
