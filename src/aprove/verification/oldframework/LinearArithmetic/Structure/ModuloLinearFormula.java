package aprove.verification.oldframework.LinearArithmetic.Structure;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class ModuloLinearFormula extends LinearFormula{

    protected Map<AlgebraVariable, Integer> coefficients;

    protected Integer constant;

    protected int modulo;

    public ModuloLinearFormula(int modulo, Map<AlgebraVariable, Integer> coefficients, Integer constant){
        this.modulo = modulo;
        this.coefficients = coefficients;
        this.constant = constant;
    }

    public ModuloLinearFormula applySubstitution(AlgebraVariable variable, int substitutionValue) {

        Map<AlgebraVariable, Integer> coeffs = this.getCoefficients();

        Integer value = coeffs.remove(variable);

        if(value == null){
            return (ModuloLinearFormula)this.deepcopy();
        }
        else{
            int addConstant = value * substitutionValue;
            int newConstant = this.constant + addConstant;

            ModuloLinearFormula newimlf = new ModuloLinearFormula(this.modulo, coeffs, newConstant);

            return newimlf;
        }
    }

    @Override
    public ModuloLinearFormula deepcopy() {
        HashMap<AlgebraVariable, Integer> newMap = new HashMap<AlgebraVariable, Integer>(this.coefficients.size());
        Set<Entry<AlgebraVariable, Integer>> entrySet = this.coefficients.entrySet();
        for (Entry<AlgebraVariable, Integer> entry : entrySet) {
            newMap.put((AlgebraVariable)entry.getKey().deepcopy(), entry.getValue().intValue());
        }

        return new ModuloLinearFormula(this.modulo, newMap, this.constant.intValue());
    }

    /**
     * @return the modulo
     */
    public int getModulo() {
        return this.modulo;
    }

    @Override
    public <T> T apply(LinearFormulaVisitor<T> fv) {
        return fv.caseModuloLinearFormula( this );
    }

    /**
     * @return Returns a copy of the coefficients.
     */
    public Map<AlgebraVariable, Integer> getCoefficients() {
        Map<AlgebraVariable, Integer> coefficientsCopy = new LinkedHashMap<AlgebraVariable, Integer>(this.coefficients.size());
        for (Entry<AlgebraVariable, Integer> entry : this.coefficients.entrySet()) {
            Integer value = entry.getValue();
            if (!value.equals(0)){
                coefficientsCopy.put(entry.getKey(), value.intValue());
            }
        }
        return coefficientsCopy;
    }

    /**
     * @return Returns a copy of the constant.
     */
    public int getConstant() {
        return this.constant.intValue();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(this.modulo);
        sb.append(" | ");

        Set<Entry<AlgebraVariable, Integer>> entries = this.coefficients.entrySet();

        Iterator<Entry<AlgebraVariable, Integer>> iterator = entries.iterator();
        Entry<AlgebraVariable, Integer> entry;

        boolean first = true;

        while (iterator.hasNext()) {
            entry = iterator.next();

            Integer value = entry.getValue();

            if (value == 0) {
                continue;
            }

            if (!first) {
                sb.append(" + ");
            }
            else {
                first = false;
            }

            if (value == -1) {
                sb.append("-");
            }
            else if (value != 1) {
                sb.append(entry.getValue());
            }
            sb.append(entry.getKey());
        }

        if (first || this.constant != 0) {
            if (!first) {
                sb.append(" + ");
            }
            sb.append(this.constant);
        }

        return sb.toString();
    }

    /**
     * Returns the variables which are used in the constraint.
     * This means which have non-zero coefficients.
     *
     * @return a set of the variables with non-zero coefficients
     */
    public Set<AlgebraVariable> getUsedVariables(){
        HashSet<AlgebraVariable> usedVariables = new HashSet<AlgebraVariable>();
        for (Entry<AlgebraVariable, Integer> entry : this.coefficients.entrySet()) {
            Integer i = entry.getValue();
            if(i != null && i != 0){
                usedVariables.add(entry.getKey());
            }
        }
        return usedVariables;
    }


    public ModuloLinearFormula applyDissolving(Dissolving dissolving) {

        AlgebraVariable disVar = dissolving.getVariable();
        Map<AlgebraVariable, Rational> disCoefficients = dissolving.getCoefficients();
        Integer disConstant = dissolving.getConstant().getNumerator();

        if(!this.getUsedVariables().contains(disVar)){
            // nothing to do
            return this.deepcopy();
        }

        Map<AlgebraVariable, Integer> newCoefficients = this.getCoefficients();
        Integer disCoef = newCoefficients.get(disVar);

        newCoefficients.remove(disVar);

        Integer newConstant = this.constant + (disConstant * disCoef);

        for (Entry<AlgebraVariable, Rational> entry : disCoefficients.entrySet()) {

            Integer r = entry.getValue().getNumerator() * disCoef;

            AlgebraVariable var = entry.getKey();
            Integer varcoef = newCoefficients.get(var);

            r = r + varcoef;

            newCoefficients.put(var, r);
        }

        return new ModuloLinearFormula(this.modulo, newCoefficients, newConstant);
    }

}
