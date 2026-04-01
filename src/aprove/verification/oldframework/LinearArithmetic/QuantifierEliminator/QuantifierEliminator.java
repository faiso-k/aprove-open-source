package aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class QuantifierEliminator implements LinearFormulaVisitor<LinearFormula>{

    private static final boolean STRONG_SIMPLIFICATION = Globals.DEBUG_DICKMEIS && false;

    @Override
    public LinearFormula caseAllQuantifiedLinearFormula(AllQuantifiedLinearFormula allLinearFormula) {
        LinearFormula subformula = allLinearFormula.getSubFormula();
        AlgebraVariable var = allLinearFormula.getVariable();

        NotLinearFormula notLinearFormula = new NotLinearFormula(subformula);

        ExistentialQuantifiedLinearFormula existential =
            new ExistentialQuantifiedLinearFormula(var, notLinearFormula);

        NotLinearFormula notResult = new NotLinearFormula(existential);

        LinearFormula result = notResult.apply(this);

        SimplificationVisitor simplify = new SimplificationVisitor();

        LinearFormula res = result.apply(simplify);

        return res;
    }

    @Override
    public LinearFormula caseAnd(AndLinearFormula and) {

        LinearFormula left = and.getLeft().apply(this);
        LinearFormula right = and.getRight().apply(this);

        return new AndLinearFormula(left, right);
    }

    @Override
    public LinearFormula caseExistentialQuantifiedLinearFormula(ExistentialQuantifiedLinearFormula existentialLinearFormula) {

        AlgebraVariable var = existentialLinearFormula.getVariable();

        LinearFormula subformula = existentialLinearFormula.getSubFormula();

        // insert nonnegative condition
        Map<AlgebraVariable, Rational> coef = new HashMap<AlgebraVariable, Rational>(1);
        coef.put(var, new Rational(1));
        LinearConstraint nonneg = new LinearConstraint(coef , ConstraintType.GREATEREQ, new Rational(0));

        AndLinearFormula nonnegsunformula = new AndLinearFormula(nonneg, subformula);

        LinearFormula newsubformula = nonnegsunformula.apply(this);

        PushNegationInsideTransformer pnif = new PushNegationInsideTransformer();
        LinearFormula literalForm = newsubformula.apply(pnif);

        ToLessTransformer tlf = new ToLessTransformer();
        LinearFormula normalForm = literalForm.apply(tlf);

        Pair<Integer, List<LinearConstraint>> p = LcmAndBGetter.apply(var, normalForm);
        int lcm = p.x;
        List<LinearConstraint> b = p.y;

        ArrayList<LinearFormula> disjunctions = new ArrayList<LinearFormula>(lcm);

        for(int j=1; j <= lcm; j++){
            ToMinusInfinityTransformer tmif = new ToMinusInfinityTransformer(var, j);
            LinearFormula mif = normalForm.apply(tmif);

            if(QuantifierEliminator.STRONG_SIMPLIFICATION){
                mif = mif.apply(new SimplificationVisitor());
            }

            disjunctions.add(mif);
        }


        LinearFormula first = null;

        for (LinearConstraint constraint : b) {

            Map<AlgebraVariable, Rational> coeffs = constraint.getCoefficients();
            Rational constant = constraint.getConstant();
            int c = - constant.getNumerator();

            Rational rk = coeffs.remove(var).negate();
            int  k = rk.getNumerator();

            Map<AlgebraVariable, Integer> t = new HashMap<AlgebraVariable, Integer>(coeffs.size());
            for (Entry<AlgebraVariable, Rational> entry : coeffs.entrySet()) {
                t.put(entry.getKey(), entry.getValue().getNumerator());
            }

            for(int j=1; j <= lcm; j++){

                LinearFormula modulo;
                if(k!=1){
                    modulo = new ModuloLinearFormula(k, t, c+j);
                }
                else{
                    modulo = TruthValueLinearFormula.TRUE;
                }

                KXSubstitutionVisitor kxSubst = new KXSubstitutionVisitor(k, var, t, c+j);

                LinearFormula elimFormula = normalForm.apply(kxSubst);

                LinearFormula and = new AndLinearFormula(modulo, elimFormula);

                if(QuantifierEliminator.STRONG_SIMPLIFICATION && first != null){
                    SimplificationVisitor simplify = new SimplificationVisitor();
                    LinearFormula newand = and.apply(simplify);

                    if(newand.equals(TruthValueLinearFormula.FALSE)){
                        continue;
                    }

                    List<Dissolving> dissolvings = ExtendedSimplificationVisitor.apply(newand);

                    if(dissolvings != null){

                        LinearFormula firstappldiss = first.apply(new DissolvingsApplicator(dissolvings));

                        LinearFormula simple = firstappldiss.apply(simplify);

                        if(simple.equals(TruthValueLinearFormula.TRUE)){
                            continue;
                        }
                    }
                }

                if(first == null){
                    first = and;
                }

                disjunctions.add(and);
            }
        }

        LinearFormula or = OrLinearFormula.create(disjunctions);


//        System.out.println("treating: " + existentialLinearFormula);
//        System.out.println("newsub: " + newsubformula);
//        System.out.println("normal: " + normalForm);
//        System.out.println("or " + or);

        SimplificationVisitor simplify = new SimplificationVisitor();

        LinearFormula res = or.apply(simplify);

//        System.out.println("res " + res + "\n\n");

        return res;
    }

    @Override
    public LinearFormula caseLinearConstraint(LinearConstraint linearConstraint) {
        return linearConstraint.deepcopy();
    }

    @Override
    public LinearFormula caseModuloLinearFormula(ModuloLinearFormula moduloLinearFormula) {
        return moduloLinearFormula.deepcopy();
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
