package aprove.verification.oldframework.LinearArithmetic.Structure;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * Representing a linear constraint like
 * a*x + b*y + c*z   >=<  d
 * no coefficient 0 is allowed
 *
 * @author dickmeis
 * @version $Id$
 */

public class LinearConstraint extends LinearFormula{

    private Map<AlgebraVariable, Rational> coefficients;

    private ConstraintType constraintType;

    private Rational constant;
    
    private final int hashCode;

    /**
     * Constructor for a linear constraint like a*x + b*y + c*z  <=  d.
     * The coefficients is a mapping from a variable to its integer coefficient.
     * The coefficients and the constants are Rationals.
     *
     * Better use only for debugging.
     *
     * @param coefficients
     * @param constraintType
     * @param constant
     */
    public LinearConstraint(Map<AlgebraVariable, Rational> coefficients,
            ConstraintType constraintType, Rational constant) {

        if(Globals.DEBUG_DICKMEIS && constraintType == null){
            System.err.println("constraintType not set.");
        }

        this.coefficients = coefficients;
        this.constraintType = constraintType;
        this.constant =  constant;
        this.hashCode = this.constraintType.hashCode() * 2 + 7039 * this.constant.hashCode();
    }

    /**
     * Constructor for a linear constraint like a*x + b*y + c*z  <=  d.
     * The coefficients is a mapping from a variable to its integer coefficient.
     * The coefficients and the constants are integers.
     *
     * @param coefficients
     * @param constraintType
     * @param constant
     */
    public LinearConstraint(Map<AlgebraVariable, Integer> coefficients,
            ConstraintType constraintType, int constant) {

        if(Globals.DEBUG_DICKMEIS && constraintType == null){
            System.err.println("constraintType not set.");
        }

        this.coefficients = new LinkedHashMap<AlgebraVariable, Rational>();
        for (Entry<AlgebraVariable, Integer> entry : coefficients.entrySet()) {
            this.coefficients.put(entry.getKey(), new Rational(entry.getValue()));
        }
        this.constraintType = constraintType;
        this.constant =  new Rational(constant);
        this.hashCode = this.constraintType.hashCode() * 2 + 7039 * this.constant.hashCode();
    }

    /**
     * Copies this object.
     *
     * @return A copy from the object.
     */
    @Override
    public LinearConstraint deepcopy(){
        Map<AlgebraVariable, Rational> coef = new LinkedHashMap<AlgebraVariable, Rational>(this.coefficients.size());
        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            coef.put(entry.getKey(), entry.getValue().deepcopy());
        }
        return new LinearConstraint(coef, this.constraintType, this.constant.deepcopy());
    }

    /**
     * @return Returns a copy of the coefficients.
     */
    public Map<AlgebraVariable, Rational> getCoefficients() {
        Map<AlgebraVariable, Rational> coefficientsCopy = new LinkedHashMap<AlgebraVariable, Rational>(this.coefficients.size());
        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            Rational value = entry.getValue();
            if (!value.equals(Rational.zero)){
                coefficientsCopy.put(entry.getKey(), value.deepcopy());
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
     * @return Returns the constraintType.
     */
    public ConstraintType getConstraintType() {
        return this.constraintType;
    }

    /**
     * Multiplicate by (-1)
     * Does not change the object itself.
     * But generates a new LinearConstraint which is the result
     * of multiplicating this wiht -1
     *
     * @return The LinearConstraint multiplicated by (-1)
     */
    public LinearConstraint timesMinusOne() {
        LinkedHashMap<AlgebraVariable, Rational> negatedCoefficients;
        negatedCoefficients = new LinkedHashMap<AlgebraVariable, Rational> (this.coefficients.size());

        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            negatedCoefficients.put(entry.getKey(), entry.getValue().negate());
        }

        ConstraintType ct = this.turnConstraintType();

        Rational negatedConstant = this.constant.negate();

        return new LinearConstraint(negatedCoefficients, ct, negatedConstant);
    }

    /**
     * Negates the constraint
     * @return The negated LinearConstraint.
     */
    public LinearConstraint negate() {
        LinearConstraint newConstraint = this.deepcopy();

        ConstraintType negatedCt = null;
        switch (this.constraintType) {
        case EQUALITY:
            negatedCt = ConstraintType.INEQUALITY;
            break;
        case INEQUALITY:
            negatedCt = ConstraintType.EQUALITY;
            break;
        case LESS:
            negatedCt = ConstraintType.GREATEREQ;
            break;
        case GREATEREQ:
            negatedCt = ConstraintType.LESS;
            break;
        case GREATER:
            negatedCt = ConstraintType.LESSEQ;
            break;
        case LESSEQ:
            negatedCt = ConstraintType.GREATER;
            break;
        default:
            break;
        }

        newConstraint.constraintType=negatedCt;

        return newConstraint;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        Set<Entry<AlgebraVariable, Rational>> entries = this.coefficients.entrySet();

        Iterator<Entry<AlgebraVariable, Rational>> iterator = entries.iterator();
        Entry<AlgebraVariable, Rational> entry;

        boolean first = true;

        while(iterator.hasNext()){
            entry = iterator.next();

            Rational value = entry.getValue();

            if(value.equals(Rational.zero)){
                continue;
            }

            if(!first){
                sb.append(" + ");
            }
            else{
                first = false;
            }

            if(value.equals(new Rational(-1))){
                sb.append("-");
            }
            else if(!value.equals(new Rational(1))){
                sb.append(value);
            }
            sb.append(entry.getKey());
        }

        sb.append(" ");
        sb.append(this.constraintType);
        sb.append(" ");
        sb.append(this.constant);

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
        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            Rational r = entry.getValue();
            if(r != null && !r.equals(Rational.zero)){
                usedVariables.add(entry.getKey());
            }
        }
        return usedVariables;
    }

    /**
     * If the constraint is an equation, the constraint is dissolved for
     * the given variable.
     *
     * @param var The variable to dissolve for.
     * @return The Dissolving of the constraint for the given variable.
     */
    public Dissolving dissolveFor(AlgebraVariable var){
        if(this.constraintType != ConstraintType.EQUALITY){
            // we are only interested in equations
            return null;
        }

        if(!this.getUsedVariables().contains(var)){
            // solving for a not occuring variable
            return null;
        }

        Rational varCoeff = this.coefficients.get(var);

        Map<AlgebraVariable, Rational> newCoefficients = new LinkedHashMap<AlgebraVariable, Rational>();
        Rational newConstant;

        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            if(var.equals(entry.getKey())){
                continue;
            }

            Rational r = entry.getValue().divideBy(varCoeff);
            newCoefficients.put(entry.getKey(), r.negate());
        }

        newConstant = this.constant.divideBy(varCoeff);


        return new Dissolving(var, newCoefficients, newConstant);
    }

    /**
     * Applies a disolving to the constraint.
     *
     * @param dissolving The dissolving to apply.
     *
     * @return the result of applying the given dissolving to this constraint.
     */
    public LinearConstraint applyDissolving(Dissolving dissolving){

        AlgebraVariable disVar = dissolving.getVariable();
        Map<AlgebraVariable, Rational> disCoefficients = dissolving.getCoefficients();
        Rational disConstant = dissolving.getConstant();

        if(!this.getUsedVariables().contains(disVar)){
            // nothing to do
            return this.deepcopy();
        }

        Map<AlgebraVariable, Rational> newCoefficients = this.getCoefficients();
        Rational disCoef = newCoefficients.get(disVar);

        newCoefficients.remove(disVar);

        Rational newConstant = this.constant.minus(disConstant.times(disCoef));

        for (Entry<AlgebraVariable, Rational> entry : disCoefficients.entrySet()) {

            Rational r = entry.getValue().times(disCoef);

            AlgebraVariable var = entry.getKey();
            Rational varcoef = newCoefficients.get(var);

            r = r.plus(varcoef);

            newCoefficients.put(var, r);
        }

        return new LinearConstraint(newCoefficients, this.constraintType, newConstant);
    }

    /**
     * Cancels the gcd from every coefficient and the constant.
     * (german: kuerzen)
     *
     * @return A copy of the LinearConstraint
     *           but with canceled coefficients and constant.
     */
    public LinearConstraint cancel() {
        Rational gcd;

        // use the absolute value
        if (this.constant.compareTo(Rational.zero) >= 0){
            gcd = this.constant;
        }
        else{
            gcd = this.constant.negate();
        }

        Set<Entry<AlgebraVariable,Rational>> coeff = this.coefficients.entrySet();
        for (Entry<AlgebraVariable, Rational> entry : coeff) {
            gcd = Rational.gcd(gcd, entry.getValue());
        }

        Map<AlgebraVariable, Rational> newCoefficients = new LinkedHashMap<AlgebraVariable, Rational>(this.coefficients.size());

        if (!gcd.equals(new Rational(1)) && !gcd.equals(Rational.zero)){
            Rational newConstant = this.constant.divideBy(gcd);
            for (Entry<AlgebraVariable, Rational> entry : coeff) {
                Rational r = entry.getValue().divideBy(gcd);
                newCoefficients.put(entry.getKey(), r);
            }

            return new LinearConstraint(newCoefficients, this.constraintType, newConstant);
        }
        else{
            return this.deepcopy();
        }
    }

    /**
     * Turn the constraint type
     *
     * @return The turned ConstraintTyp
     */
    private ConstraintType turnConstraintType(){
        if (this.constraintType == ConstraintType.GREATEREQ){
            return ConstraintType.LESSEQ;
        }
        else if (this.constraintType == ConstraintType.LESSEQ){
            return ConstraintType.GREATEREQ;
        }
        else if (this.constraintType == ConstraintType.GREATER){
            return ConstraintType.LESS;
        }
        else if (this.constraintType == ConstraintType.LESS){
            return ConstraintType.GREATER;
        }
        else{
            return this.constraintType;
        }
    }

    /**
     * Checks whether this is an integer constraint.
     * This means that every coefficient and the constant are integers
     *
     * @return true iff this is an integer constraint.
     */
    public boolean isInteger() {
        if(this.constant.getDenominator() != 1){
            if(Globals.DEBUG_DICKMEIS){
                System.out.println(this + " is not an integer constraint.");
            }
            return false;
        }
        Set<Entry<AlgebraVariable, Rational>> coeffs = this.coefficients.entrySet();
        for (Entry<AlgebraVariable, Rational> entry : coeffs) {
            if(entry.getValue().getDenominator() != 1){
                if(Globals.DEBUG_DICKMEIS){
                    System.out.println(this + " is not an integer constraint.");
                }
                return false;
            }
        }

        return true;
    }

    /**
     * Change the constraint type.
     *
     * @param constraintType The ConstraintType to change into.
     * @return A copy of the LinearConstraint but with changed ConstraintType
     */
    public LinearConstraint changeConstraintType(ConstraintType constraintType) {
        LinearConstraint change = this.deepcopy();
        change.constraintType = constraintType;
        return change;
    }

    /**
     * Creates a LinearConstraint for left = right.
     *
     * @param left the left term.
     * @param right the right term.
     * @param laProgram Background information about the properties of LA
     *
     * @return the corresponding constraint with type equality
     */
    public static LinearConstraint createEquation(AlgebraTerm left, AlgebraTerm right, LAProgramProperties laProgram) {
        LinearTermNormalizer ltnLeft = new LinearTermNormalizer(laProgram);
        left.apply(ltnLeft);
        LinearTermNormalizer ltnRight = new LinearTermNormalizer(laProgram);
        right.apply(ltnRight);

        if(!ltnLeft.isLinearTerm() || !ltnRight.isLinearTerm()){
            return null;
        }

        if(ltnLeft.getConstraintType() != null || ltnRight.getConstraintType() != null){
            return null;
        }

        int constant = ltnLeft.getConstant() - ltnRight.getConstant();

        Map<AlgebraVariable, Integer> leftCoeff = ltnLeft.getCoefficients();
        Map<AlgebraVariable, Integer> rightCoeff = ltnRight.getCoefficients();
        Map<AlgebraVariable, Integer> coeff = new LinkedHashMap<AlgebraVariable, Integer>(leftCoeff.size());

        for (Entry<AlgebraVariable, Integer> entry : leftCoeff.entrySet()) {
            AlgebraVariable var = entry.getKey();
            Integer lValue = entry.getValue();
            Integer rValue = rightCoeff.get(var);

            if(rValue == null){
                rValue = 0;
            }
            else{
                rightCoeff.remove(var);
            }

            Integer value = lValue - rValue;
            coeff.put(var, value);
        }
        for (Entry<AlgebraVariable, Integer> entry : rightCoeff.entrySet()) {
            AlgebraVariable var = entry.getKey();
            Integer rValue = entry.getValue();

            coeff.put(var, -rValue);
        }


        return new LinearConstraint(coeff, ConstraintType.EQUALITY, constant);
    }

    @Override
    public int hashCode() {
        return hashCode();
    }

    @Override
    public boolean equals(Object o){
        if (o== null){
            return false;
        }

        if (o instanceof LinearConstraint) {
            LinearConstraint that = (LinearConstraint) o;

            if (!this.constraintType.equals(that.getConstraintType())
                   || !this.constant.equals(that.getConstant())){
                return false;
            }

            Set<AlgebraVariable> thisvars = this.getUsedVariables();
            Set<AlgebraVariable> thatvars = that.getUsedVariables();

            for (AlgebraVariable variable : thatvars) {
                Rational thatr = that.coefficients.get(variable);
                Rational thisr = this.coefficients.get(variable);

                if(!thatr.equals(thisr)){
                    return false;
                }
                thisvars.remove(variable);
            }

            for (AlgebraVariable variable : thisvars) {
                Rational thatr = that.coefficients.get(variable);
                Rational thisr = this.coefficients.get(variable);

                if(!thisr.equals(thatr)){
                    return false;
                }
            }

            return true;
        }

        return false;
    }

    /**
     * Creates a linear constraint from an equation
     *
     * @param eq The equation to transform
     * @param laProgram Background information about the properties of LA
     *
     * @return The corresponding linear constraint
     */
    public static LinearConstraint create(Equation eq, LAProgramProperties laProgram){

        LinearTermNormalizer ltn = new LinearTermNormalizer(laProgram);
        boolean linearTerm;
        LinearConstraint constraint = null;

        ConstructorApp tFalse = ConstructorApp.create(laProgram.csFalse);

        AlgebraTerm left = eq.getLeft();
        AlgebraTerm right = eq.getRight();

        if (right.getSort().equals(laProgram.sortBool)){

            if (right instanceof ConstructorApp) {

                left.apply(ltn);
                linearTerm = ltn.isLinearTerm();
                if(linearTerm){
                    constraint = ltn.getConstraint();
                    if (right.equals(tFalse)){
                        constraint = constraint.negate();
                    }
                }
            }
            else if(left instanceof ConstructorApp) {

                right.apply(ltn);
                linearTerm = ltn.isLinearTerm();
                if(linearTerm){
                    constraint = ltn.getConstraint();
                    if (left.equals(tFalse)){
                        constraint = constraint.negate();
                    }
                }
            }
            else{
                // error
                return null;
            }
        }
        else if (eq.getRight().getSort().equals(laProgram.sortNat)){
            constraint = LinearConstraint.createEquation(eq.getLeft(), eq.getRight(), laProgram);
            if(constraint == null){
                // error
                return null;
            }
        }
        else{
            // error
            return null;
        }

        return constraint;
    }

    /**
     * Multiplies a constraint with a scalar factor
     *
     * @param f the scalar factor
     * @return a new constraint
     */
    public LinearConstraint scalarMultiply(Rational f) {
        if(f.equals(Rational.zero)){
            return new LinearConstraint(new LinkedHashMap<AlgebraVariable, Rational>(), this.constraintType, Rational.zero);
        }

        Rational newConstant = this.constant.times(f);

        Map<AlgebraVariable, Rational> newCoefficients = new LinkedHashMap<AlgebraVariable, Rational>(this.coefficients.size());

        Set<Entry<AlgebraVariable,Rational>> coeff = this.coefficients.entrySet();

        for (Entry<AlgebraVariable, Rational> entry : coeff) {
            Rational nr = entry.getValue().times(f);
            newCoefficients.put(entry.getKey(), nr);
        }

        LinearConstraint newConstraint = new LinearConstraint(newCoefficients, this.constraintType, newConstant);

        if(f.isPositive()){
            return newConstraint;
        }
        else{
            newConstraint.constraintType = newConstraint.turnConstraintType();
            return newConstraint;
        }
    }

    /**
     * adds to the current constraint another resulting in a new constraint
     * note: both constraints MUST have type <=
     *
     * @param that the constraint to add
     * @return constraint being the sum of the two
     */
    public LinearConstraint addConstraint(LinearConstraint that) {
        if(!this.constraintType.equals(ConstraintType.LESSEQ) ||
                !that.constraintType.equals(ConstraintType.LESSEQ)){
            throw new RuntimeException("Not able to add constraints not having type <=");
        }

        Rational newConstant = this.constant.plus(that.constant);

        Map<AlgebraVariable, Rational> newCoefficients = new LinkedHashMap<AlgebraVariable, Rational>(this.coefficients.size());

        Set<Entry<AlgebraVariable,Rational>> coeff = this.coefficients.entrySet();

        Set<AlgebraVariable> thatVars = that.getUsedVariables();

        for (Entry<AlgebraVariable, Rational> entry : coeff) {
            AlgebraVariable var = entry.getKey();

            Rational nr = entry.getValue();

            Rational r2 = that.coefficients.get(var);

            if(r2 == null){
                newCoefficients.put(var, nr);
            }
            else{
                nr = nr.plus(r2);

                if(!nr.equals(Rational.zero)){
                    newCoefficients.put(var, nr);
                }

                thatVars.remove(var);
            }
        }

        for (AlgebraVariable var : thatVars) {
            Rational nr = that.coefficients.get(var);
            newCoefficients.put(var, nr);
        }

        return new LinearConstraint(newCoefficients, ConstraintType.LESSEQ, newConstant);

    }

    @Override
    public <T> T apply(LinearFormulaVisitor<T> fv) {
        return fv.caseLinearConstraint( this );
    }

    public LinearConstraint toInteger(){
        int lcm = this.constant.getDenominator();

        for (Entry<AlgebraVariable, Rational> entry : this.coefficients.entrySet()) {
            lcm = Rational.lcm(lcm, entry.getValue().getDenominator());
        }

        LinearConstraint newConstraint;

        if(lcm != 1){
            newConstraint = this.scalarMultiply(new Rational(lcm));
        }
        else{
            newConstraint = this.deepcopy();
        }

        return newConstraint;
    }
}
