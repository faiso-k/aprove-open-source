package aprove.verification.oldframework.LinearArithmetic;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * Some helper functions.
 * This works only when you are operationg on INTEGER values.
 *
 * @author dickmeis
 * @version $Id$
 */

public class LinearIntegerHelper {

    /**
     * Transforms a linear integer(!) constraint to an equation
     *
     * @param constraint The constraint to transform.
     * @param laProgram Background information about the properties of LA
     *
     * @return the corresponding equation.
     */
    public static Equation toEquation(LinearConstraint constraint, LAProgramProperties laProgram){
        Map<AlgebraVariable, Rational> coefficients = constraint.getCoefficients();

        Map<AlgebraVariable, Rational> positive = new LinkedHashMap<AlgebraVariable, Rational>(coefficients.size());
        Map<AlgebraVariable, Rational> negative = new LinkedHashMap<AlgebraVariable, Rational>(coefficients.size());

        for (Entry<AlgebraVariable, Rational> entry : coefficients.entrySet()) {
            if(entry.getValue().compareTo(Rational.zero) > 0){
                positive.put(entry.getKey(), entry.getValue());
            }
            else{
                negative.put(entry.getKey(), entry.getValue());
            }
        }

        AlgebraTerm left = LinearIntegerHelper.toTerm(positive, laProgram);
        AlgebraTerm right = LinearIntegerHelper.toTerm(negative, laProgram);

        // as we deal with integers we take the numerator
        int constant = constraint.getConstant().getNumerator();

//        if (constant >= 0){
//            Term number = ConstructorApp.create(laProgram.csZero);
//            for (int i = 0; i < constant; i++) {
//                Term[] args = {number};
//                number = ConstructorApp.create(laProgram.csSucc, args);
//            }
//            Term[] args = {right, number};
//            right = DefFunctionApp.create(laProgram.fsPlus, args);
//        }
        if (constant >= 0){
            for (int i = 0; i < constant; i++) {
                AlgebraTerm[] args = {right};
                right = ConstructorApp.create(laProgram.csSucc, args);
            }
        }
        else {
            // if (constant < 0){
            for (int i = 0; i > constant; i--) {
                AlgebraTerm[] args = {left};
                left = AlgebraFunctionApplication.create(laProgram.csSucc, args);
            }
        }

        AlgebraTerm lhs = null;
        AlgebraTerm[] args = {left, right};
        switch (constraint.getConstraintType()) {
        case EQUALITY:
            lhs = DefFunctionApp.create(laProgram.fsEqual, args);
            break;
        case INEQUALITY:
            lhs = DefFunctionApp.create(laProgram.fsInequal, args);
            break;
        case LESS:
            lhs = DefFunctionApp.create(laProgram.fsLess, args);
            break;
        case LESSEQ:
            lhs = DefFunctionApp.create(laProgram.fsLesseq, args);
            break;
        case GREATER:
            lhs = DefFunctionApp.create(laProgram.fsGreater, args);
            break;
        case GREATEREQ:
            lhs = DefFunctionApp.create(laProgram.fsGreatereq, args);
            break;
        }

        AlgebraTerm rhs = ConstructorApp.create(laProgram.csTrue);
        Equation eq = Equation.create(lhs, rhs);

        return eq;
    }

    /**
     * Transforms the integer(!) coefficients to a term.
     *
     * @param coefficients the coefficients to transform.
     * @param laProgram Background information about the properties of LA
     *
     * @return The corresponding term.
     */
    public static AlgebraTerm toTerm(Map<AlgebraVariable, Rational> coefficients, LAProgramProperties laProgram){

        if(coefficients.isEmpty()){
            return ConstructorApp.create(laProgram.csZero);
        }

        Iterator<Entry<AlgebraVariable, Rational>> iterator = coefficients.entrySet().iterator();
        Entry<AlgebraVariable, Rational> entry = iterator.next();

        AlgebraVariable covar = entry.getKey();
        AlgebraTerm term = covar;

        int coeff = entry.getValue().getNumerator() - 1;

        while(coeff > 0){
            AlgebraTerm[] args = {term, covar};
            term = AlgebraFunctionApplication.create(laProgram.fsPlus, args);
            coeff--;
        }

        while(iterator.hasNext()){
            entry = iterator.next();

            covar = entry.getKey();
            AlgebraTerm[] args = {term, covar};
            term = AlgebraFunctionApplication.create(laProgram.fsPlus, args);

            coeff = entry.getValue().getNumerator() - 1;

            while(coeff > 0){
                AlgebraTerm[] args2 = {term, covar};
                term = AlgebraFunctionApplication.create(laProgram.fsPlus, args2);
                coeff--;
            }
        }

        return term;
    }

    /**
     * Transforms the integer(!) coefficients plus an integer constant into a term.
     *
     * @param coefficients the coefficients to transform.
     * @param constant the constant to transform.
     * @param laProgram Background information about the properties of LA
     *
     * @return The corresponding term.
     */
    public static AlgebraTerm toTerm(Map<AlgebraVariable, Rational> coefficients, Rational constant, LAProgramProperties laProgram){
        AlgebraTerm t = LinearIntegerHelper.toTerm(coefficients, laProgram);

        // as we deal with integers we take the numerator
        int c = constant.getNumerator();

        for (int i = 0; i < c; i++) {
            AlgebraTerm[] args = {t};
            t = ConstructorApp.create(laProgram.csSucc, args);
        }

        return t;
    }


    /**
     * Transforms a list of dissolvings into a substitution.
     *
     * @param dissolvings The list of dissolvings to transform
     * @param laProgram properties of LA as background information
     * @return the corresponding substitution
     */
    public static AlgebraSubstitution toSubstitution(List<Dissolving> dissolvings, LAProgramProperties laProgram){

        AlgebraSubstitution subst = AlgebraSubstitution.create();
        for (Dissolving dissolving : dissolvings) {
            AlgebraVariable var = dissolving.getVariable();
            Map<AlgebraVariable, Rational> coefficients = dissolving.getCoefficients();

            Rational constant = dissolving.getConstant();
            AlgebraTerm term = LinearIntegerHelper.toTerm(coefficients, constant, laProgram);

            subst.put(var.getVariableSymbol(), term);
        }

        return subst;
    }

}
