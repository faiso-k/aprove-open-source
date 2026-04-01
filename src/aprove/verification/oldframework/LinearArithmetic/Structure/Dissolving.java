package aprove.verification.oldframework.LinearArithmetic.Structure;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * It represents an equation of the form x = b*y + c*z + d
 *
 * @author dickmeis
 * @version $Id$
 */

public class Dissolving {

    private AlgebraVariable var;

    private Map<AlgebraVariable, Rational> coefficients;

    private Rational constant;

    /**
     * Creates a dissolving of the form x = b*y + c*z + d
     *
     * @param var
     * @param coefficients
     * @param constant
     */
    public Dissolving(AlgebraVariable var, Map<AlgebraVariable, Rational> coefficients,
            Rational constant) {
        this.var = var;
        this.coefficients = coefficients;
        this.constant = constant;
    }

    /**
     * @return Returns the variable.
     */
    public AlgebraVariable getVariable() {
        return this.var;
    }

    /**
     * @return Returns a copy of the coefficients
     *         for the used variables.
     *         Hence all coefficients are != 0.
     */
    public Map<AlgebraVariable, Rational> getCoefficients() {
        Map<AlgebraVariable, Rational> coefficientsCopy = new LinkedHashMap<AlgebraVariable, Rational>(this.coefficients.size());
        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            Rational r = entry.getValue();
            if(!r.equals(Rational.zero)){
                coefficientsCopy.put(entry.getKey(), r.deepcopy());
            }
        }
        return coefficientsCopy;
    }

    /**
     * @return Returns a copy of the constant.
     */
    public Rational getConstant() {
        return this.constant.deepcopy();
    }

    /**
     * Returns the variables which are used in the constraint. This means which
     * have non-zero coefficients.
     *
     * @return a set of the variables with non-zero coefficients
     */
    public Set<AlgebraVariable> getUsedVariables() {
        HashSet<AlgebraVariable> usedVariables = new HashSet<AlgebraVariable>();
        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            if (!entry.getValue().equals(Rational.zero)) {
                usedVariables.add(entry.getKey());
            }
        }
        return usedVariables;
    }

    /**
     * Applies a disolving to this dissolving constraint
     * The dissolving itself is not changed.
     *
     * @param dissolving
     *            The dissolving to apply.
     * @return The resulting new dissolving of the application
     *            of the dissolving to this dissolving.
     */
    public Dissolving applyDissolving(Dissolving dissolving) {
        AlgebraVariable disVar = dissolving.getVariable();
        Map<AlgebraVariable, Rational> disCoefficients = dissolving.getCoefficients();
        Rational disConstant = dissolving.getConstant();

        if (!this.getUsedVariables().contains(disVar)) {
            // nothing to do
            return this.deepcopy();
        }

        Rational disCoef = this.coefficients.get(disVar);

        Map<AlgebraVariable, Rational> newCoefficients = this.getCoefficients();

        newCoefficients.remove(disVar);

        Rational newConstant = this.constant.plus(disConstant.times(disCoef));

        for (Entry<AlgebraVariable, Rational> entry : disCoefficients.entrySet()) {

            Rational r = entry.getValue().times(disCoef);

            AlgebraVariable var = entry.getKey();
            Rational varcoef = newCoefficients.get(var);

            r = r.plus(varcoef);

            newCoefficients.put(var, r);
        }

        return new Dissolving(this.var, newCoefficients, newConstant);

    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(this.var);
        sb.append(" = ");

        Set<Entry<AlgebraVariable, Rational>> entries = this.coefficients.entrySet();

        Iterator<Entry<AlgebraVariable, Rational>> iterator = entries.iterator();
        Entry<AlgebraVariable, Rational> entry;

        boolean first = true;

        while (iterator.hasNext()) {
            entry = iterator.next();

            Rational value = entry.getValue();

            if (value.equals(Rational.zero)) {
                continue;
            }

            if (!first) {
                sb.append(" + ");
            }
            else {
                first = false;
            }

            if (value.equals(new Rational(-1))) {
                sb.append("-");
            }
            else if (!value.equals(new Rational(1))) {
                sb.append(entry.getValue());
            }
            sb.append(entry.getKey());
        }

        if (first || !this.constant.equals(Rational.zero)) {
            if (!first) {
                sb.append(" + ");
            }
            sb.append(this.constant);
        }

        return sb.toString();
    }

    public Dissolving deepcopy() {
        Map<AlgebraVariable, Rational> newCoefficients = new LinkedHashMap<AlgebraVariable, Rational>(this.coefficients.size());

        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            newCoefficients.put(entry.getKey(), entry.getValue().deepcopy());
        }

        return new Dissolving(this.var, newCoefficients, this.constant.deepcopy());
    }


    /**
     * Transforms this dissolving into a constraint
     * or more precisely into an equation
     *
     * @return The equation
     */
    public LinearConstraint toEquation() {
        Map<AlgebraVariable, Rational> coeff = new LinkedHashMap<AlgebraVariable, Rational>(this.coefficients.size()+1);

        coeff.put(this.var, new Rational(1));

        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            coeff.put(entry.getKey(), entry.getValue().negate());
        }

        return new LinearConstraint(coeff,
                ConstraintType.EQUALITY,
                this.constant.deepcopy());
    }

    /**
     * Transforms the right hand side of this dissolving into a term.
     *
     * @param laProgram Background information about the properties of LA
     *
     * @return The term representing the right hand side of the dissolving.
     */
    public AlgebraTerm rhsToTerm(LAProgramProperties laProgram) {

        AlgebraTerm t = LinearIntegerHelper.toTerm(this.coefficients,this.constant, laProgram);

        return t;
    }

}
