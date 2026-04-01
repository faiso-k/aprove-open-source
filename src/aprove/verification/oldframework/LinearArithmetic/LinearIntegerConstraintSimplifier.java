package aprove.verification.oldframework.LinearArithmetic;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This simplifies a set of linear integer constraints.
 * It can detect if the constraints are not satisfiable.
 *
 * @author dickmeis
 * @version $Id: LinearConstraintSimplifier.java,v 1.1 2006/07/25 11:03:49
 *          dickmeis Exp $
 */

public class LinearIntegerConstraintSimplifier {

    private static final boolean DEBUG = Globals.DEBUG_DICKMEIS && false;

    // constraints with type <, >, >=, <=
    private ArrayList<LinearConstraint> constraints;

    // constraints with type !=
    private ArrayList<LinearConstraint> inequations;

    // constraints with type =
    private ArrayList<LinearConstraint> equations;

    private ArrayList<Dissolving> dissolvings;

    // all variables in the list are prefered for dissolving
    // compared to otherVariables and to the following variables in the list
    private List<AlgebraVariable> preferedVariables;

    // all occuring Varaibles including the prefered
    private List<AlgebraVariable> allVariables;

    /**
     * Constructor for a LinearConstraintSimplifier.
     * There are no perefered variables for dissolving.
     * The constraints are no initially constraints. They can be extended by
     * the addConstraint method.
     */
    public LinearIntegerConstraintSimplifier() {
        this(new ArrayList<AlgebraVariable>(), new ArrayList<LinearConstraint>(), null);
    }

    /**
     * Constructor for a LinearConstraintSimplifier. The list variableOrdering
     * gives the priority of a variable when it comes to dissolve an equation
     * for a variable. The first variable in the list has the highest priority.
     * The constraints are no initially constraints. They can be extended by
     * the addConstraint method.
     *
     * @param preferedVariables
     *            List of variables indicating their priority when an equation
     *            is dissolved for a variable. The first variable in the list
     *            has the highest priority.
     */
    public LinearIntegerConstraintSimplifier(List<AlgebraVariable> preferedVariables) {
        this.constraints = new ArrayList<LinearConstraint>();
        this.equations = new ArrayList<LinearConstraint>();
        this.dissolvings = new ArrayList<Dissolving>();
        this.inequations = new ArrayList<LinearConstraint>();

        this.preferedVariables = preferedVariables;
        this.allVariables = new ArrayList<AlgebraVariable>(preferedVariables);
    }

    /**
     * Constructor for a LinearConstraintSimplifier. The list variableOrdering
     * gives the priority of a variable when it comes to dissolve an equation
     * for a variable. The first variable in the list has the highest priority.
     * The constraints are the initially constraints. They can be extended by
     * the addConstraint method.
     *
     * @param preferedVariables
     *            Set of variables indicating their priority when an equation
     *            is dissolved for a variable. They have alle the same prority.
     */
    public LinearIntegerConstraintSimplifier(Set <AlgebraVariable> preferedVariables) {
        this(new ArrayList<AlgebraVariable>(preferedVariables), new ArrayList<LinearConstraint>(), null);
    }

    /**
     * Constructor for a LinearConstraintSimplifier. The list variableOrdering
     * gives the priority of a variable when it comes to dissolve an equation
     * for a variable. The first variable in the list has the highest priority.
     * The constraints are the initially constraints. They can be extended by
     * the addConstraint method.
     *
     * @param preferedVariables
     *            List of variables indicating their priority when an equation
     *            is dissolved for a variable. The first variable in the list
     *            has the highest priority.
     * @param constraints
     *            the initial constraints
     */
    public LinearIntegerConstraintSimplifier(List<AlgebraVariable> preferedVariables,
            List<LinearConstraint> constraints) {
        this(preferedVariables, constraints, null);
    }

    /**
     * Constructor for a LinearConstraintSimplifier. The list variableOrdering
     * gives the priority of a variable when it comes to dissolve an equation
     * for a variable. The first variable in the list has the highest priority.
     * The constraints are the initially constraints. They can be extended by
     * the addConstraint method. The dissolvings are the initial dissolvings.
     *
     * @param preferedVariables
     *            List of variables indicating their priority when an equation
     *            is dissolved for a variable. The first variable in the list
     *            has the highest priority.
     * @param constraints
     *            the initial constraints
     * @param dissolvings
     *            the initial dissolvings
     */
    public LinearIntegerConstraintSimplifier(List<AlgebraVariable> preferedVariables,
            List<LinearConstraint> constraints, List<Dissolving> dissolvings) {

        this.preferedVariables = preferedVariables;
        this.allVariables = new ArrayList<AlgebraVariable>(preferedVariables);

        int consSize = constraints.size();

        this.constraints = new ArrayList<LinearConstraint>(consSize);
        this.equations = new ArrayList<LinearConstraint>(consSize);
        this.inequations = new ArrayList<LinearConstraint>(consSize);

        this.dissolvings = new ArrayList<Dissolving>();

        HashSet<AlgebraVariable> additionalVariables = new HashSet<AlgebraVariable>();

        for (LinearConstraint constraint : constraints) {
            this.addConstraint(constraint);
        }

        if(dissolvings != null){
            for (Dissolving diss : dissolvings) {
                this.dissolvings.add(diss.deepcopy());
                additionalVariables.add(diss.getVariable());
                additionalVariables.addAll(diss.getUsedVariables());
            }
        }

        additionalVariables.removeAll(this.allVariables);

        this.allVariables.addAll(additionalVariables);
    }

    /**
     * @return Returns the dissolvings.
     */
    public ArrayList<Dissolving> getDissolvings() {
        return this.dissolvings;
    }

    /**
     * Simplifies the set of constraints.
     * Possibly simple contradictions are detected
     * which make the constraints unsatisfiable.
     * In this case false is returned
     *
     * @return false if contradictions are detected which make the constraints unsatisfiable.
     */
    public boolean simplify() {
        boolean satisfiable;

        /*
         * insert non negative conditions for every variable
         */
        for (AlgebraVariable variable : this.allVariables) {
            Map<AlgebraVariable, Rational> coef = new LinkedHashMap<AlgebraVariable, Rational>(1);
            coef.put(variable, new Rational(1));
            LinearConstraint c = new LinearConstraint(coef, ConstraintType.GREATEREQ,new Rational());
            this.constraints.add(c);
        }

        // Transforms the constraints into a <= form
        this.toInteger();

        this.gaussTransformation();

        satisfiable = this.removeTautologies();
        if (satisfiable == false) {
            return false;
        }

        this.detectImplicitEquality();

        this.gaussTransformation();

        satisfiable = this.removeTautologies();
        if (satisfiable == false) {
            return false;
        }

        this.removeSyntacticRedundancy();

        satisfiable = this.removeIndependentRedundancy();
        if (satisfiable == false) {
            return false;
        }

        this.cancle();


        this.dissolvingsToPlusTransform();

        this.dissolvingsToInteger();

        this.constraintsToIntTransform();


        // delete all constraints of the form -ax -by ... <= c with c>=0
        // this is implied in LA
        int size = this.constraints.size();
        for(int i = 0; i < size; i++){
            LinearConstraint cons = this.constraints.get(i);
            Rational constant = cons.getConstant();
            boolean relevant = false;
            if(constant.compareTo(Rational.zero) >= 0){
                Map<AlgebraVariable, Rational> coef = cons.getCoefficients();
                for (Entry<AlgebraVariable, Rational> entry : coef.entrySet()) {
                    Rational r = entry.getValue();
                    if (r.compareTo(Rational.zero) > 0){
                        relevant = true;
                        break;
                    }
                }
            }
            else{
                relevant = true;
            }

            if(!relevant){
                this.constraints.remove(i);
                i--;
                size--;
            }

        }

        // remove duplicate inequations
        size = this.inequations.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint c1 = this.inequations.get(i);
            for (int j = i+1; j < size; j++) {
                LinearConstraint c2 = this.inequations.get(i);

                if(c1.equals(c2)){
                    this.inequations.remove(j);
                    j--;
                    size--;
                }
            }
        }

        return true;
    }

    /**
     * Transforms the possible rational dissolvings to integer dissolvings
     * by inserting new variables and dissolvings.
     *
     * x = (n/d) * y
     *
     * x = n * q
     * y = d * q
     */
    private void dissolvingsToInteger(){

        ArrayList<Dissolving> dis2rem = new ArrayList<Dissolving>();
        for (Dissolving dissolving : this.dissolvings) {
            int denom = dissolving.getConstant().getDenominator();
            if(denom != 1){
                LinearConstraint eq = dissolving.toEquation();
                this.equations.add(eq);
                dis2rem.add(dissolving);
                continue;
            }

            int one = 0;
            for (Entry<AlgebraVariable, Rational> e: dissolving.getCoefficients().entrySet()){
                Rational r = e.getValue();
                int d = r.getDenominator();
                if (d != 1){
                    if(one >= 1){
                        LinearConstraint eq = dissolving.toEquation();
                        this.equations.add(eq);
                        dis2rem.add(dissolving);
                        continue;
                    }
                    one++;
                }
            }

        }
        this.dissolvings.removeAll(dis2rem);

        int size = this.dissolvings.size();
        for (int index = 0; index < size; index++) {
            Dissolving dissolving = this.dissolvings.get(index);
            Map<AlgebraVariable, Rational> coeff = dissolving.getCoefficients();
            Set<AlgebraVariable> usedVariables = dissolving.getUsedVariables();

            for (AlgebraVariable var: usedVariables) {
                Rational r = coeff.get(var);
                int d = r.getDenominator();

                if (d != 1){

                    FreshVarGenerator fvg = new FreshVarGenerator(this.allVariables);

                    VariableSymbol vDs = VariableSymbol.create("Q", var.getSort());
                    AlgebraVariable vD = AlgebraVariable.create(vDs);
                    AlgebraVariable newVar = fvg.getFreshVariable(vD, false);
                    this.allVariables.add(newVar);

                    Map<AlgebraVariable, Rational> newDissolvingCoeffs = new LinkedHashMap<AlgebraVariable, Rational>();
                    newDissolvingCoeffs.put(newVar, new Rational(d));
                    Dissolving newDissolving = new Dissolving(var, newDissolvingCoeffs, new Rational());

                    if(LinearIntegerConstraintSimplifier.DEBUG){
                        System.out.println("Dissolving to change: " + dissolving);
                        System.out.println("New: " + newDissolving);
                    }

                    this.applyDissolving(newDissolving);

                    if (LinearIntegerConstraintSimplifier.DEBUG){
                        System.out.println("Changed: " + this.dissolvings.get(index));
                    }

                    this.dissolvings.add(newDissolving);
                    size++;
                }
            }
        }

        return;
    }

    /**
     * Applies the given dissolving to all constraints and dissolvings
     *
     * @param dissolving the dissolvings to apply
     */
    private void applyDissolving(Dissolving dissolving){
        int size;

        size = this.dissolvings.size();
        for (int i = 0; i < size; i++) {
            Dissolving diss = this.dissolvings.get(i);
            diss = diss.applyDissolving(dissolving);
            this.dissolvings.set(i, diss);
        }

        size = this.constraints.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint constraint = this.constraints.get(i);
            constraint = constraint.applyDissolving(dissolving);
            this.constraints.set(i, constraint);
        }

        size = this.inequations.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint constraint = this.inequations.get(i);
            constraint = constraint.applyDissolving(dissolving);
            this.inequations.set(i, constraint);
        }

        size = this.equations.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint constraint = this.equations.get(i);
            constraint = constraint.applyDissolving(dissolving);
            this.equations.set(i, constraint);
        }
    }



    /**
     * Cancels the gcd from every coefficient and the constant.
     * (german: kuerzen)
     */
    private void cancle() {
        int size;

        size = this.constraints.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint constraint = this.constraints.get(i);
            constraint = constraint.cancel();
            this.constraints.set(i, constraint);
        }

        size = this.inequations.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint constraint = this.inequations.get(i);
            constraint = constraint.cancel();
            this.inequations.set(i, constraint);
        }
    }

    /**
     * Removes independent constraints
     *
     * @return false if contradictions have been determined
     */
    private boolean removeIndependentRedundancy() {

        int consSize = this.constraints.size();

        if (consSize <= 1) {
            // nothing to do
            return true;
        }

        ArrayList<LinearConstraint> redundantConstraints = new ArrayList<LinearConstraint>(
                consSize);

        for (int i = 0; i < consSize; i++) {

            LinearConstraint cons = this.constraints.get(i);
            SimplexBuilder simbu = new SimplexBuilder();

            for (int j = 0; j < consSize; j++) {
                if (i != j) {
                    simbu.addConstraint(this.constraints.get(j));
                }
            }

            simbu.setGoalFunction(cons.getCoefficients());
            Simplex sim = simbu.buildSimplexTable();
            Rational result = sim.solve();

            if(!sim.isSatisfiable()){
                return false;
            }

            if (!sim.isUnrestricted()
                    && result.compareTo(cons.getConstant()) <= 0) {
                // redundant
                redundantConstraints.add(cons);
            }
        }

        this.constraints.removeAll(redundantConstraints);

        return true;
    }

    /**
     * Removes syntactic redundant constraints
     */
    public void removeSyntacticRedundancy() {
        int consSize = this.constraints.size();

        // i < constraints.size()-1 has been written by intention
        outer : for (int i = 0; i < consSize - 1; i++) {

            LinearConstraint c1 = this.constraints.get(i);

            for (int j = i + 1; j < consSize; j++) {
                LinearConstraint c2 = this.constraints.get(j);

                Rational gamma = this.compareCoefficients(c1, c2);

                if (gamma != null) {
                    // there is redundancy

                    Rational r1 = c1.getConstant();
                    Rational r2 = c2.getConstant();

                    Rational r = r1.times(gamma);
                    if (r2.compareTo(r) < 0) {
                        this.constraints.remove(i);
                        i--;
                        consSize--;

                        continue outer;
                    }
                    else {
                        this.constraints.remove(j);
                        j--;
                        consSize--;
                    }
                }
            }
        }

    }

    /**
     * Compares the coefficients of two constraint.
     * It searches for a positive scalar gamma such that
     * gamma * c1 = c2
     * If possible gamma is returned otherwise null
     *
     * @param c1
     * @param c2
     * @return A positive scalar gamma such that gamma * c1 = c2
     *          otherwise null.
     */
    private Rational compareCoefficients(LinearConstraint c1, LinearConstraint c2) {

        Set<AlgebraVariable> c1Variables = c1.getUsedVariables();
        Set<AlgebraVariable> c2Variables = c2.getUsedVariables();

        if (!c1Variables.equals(c2Variables)) {
            // no redundancy
            return null;
        }

        Map<AlgebraVariable, Rational> c1Coefficients = c1.getCoefficients();
        Map<AlgebraVariable, Rational> c2Coefficients = c2.getCoefficients();

        Rational gamma = null;

        for (AlgebraVariable var : c1Variables) {
            Rational r1 = c1Coefficients.get(var);
            Rational r2 = c2Coefficients.get(var);

            if (gamma == null) {
                // first get a candiate to compare
                gamma = r2.divideBy(r1);
                if (gamma.compareTo(Rational.zero) < 0) {
                    // there is no positive skalar
                    return null;
                }
            }
            else {
                // compare
                Rational r = r1.times(gamma);
                if (!r.equals(r2)) {
                    // constraints are not equal
                    return null;
                }
            }
        }

        return gamma;
    }

    /**
     * Detects implicit equalities
     * and adds them to the equations
     *
     * @return true iff implicit equalities have been detected.
     */
    private boolean detectImplicitEquality() {

        SimplexBuilder simbu = null;
        Simplex sim = null;
        Rational result = null;

        Iterator<LinearConstraint> constraintIterator = this.constraints.iterator();

        ArrayList<LinearConstraint> redundantConstraints = new ArrayList<LinearConstraint>(
                this.constraints.size());

        while (constraintIterator.hasNext()) {
            LinearConstraint constraint = constraintIterator.next();

            simbu = new SimplexBuilder(this.constraints);

//            for (LinearConstraint e : equations) {
//                simbu.addConstraint(e);
//            }
//            for (Dissolving d : dissolvings){
//                simbu.addConstraint(d.toEquation());
//            }

            // negate coefficients & constant to solve a max problem instead of
            // a min problem
            Map<AlgebraVariable, Rational> coef = constraint.getCoefficients();
            Map<AlgebraVariable, Rational> goalFunction = new LinkedHashMap<AlgebraVariable, Rational>(
                    coef.size());

            for (Entry<AlgebraVariable, Rational> entry : coef.entrySet()) {
                AlgebraVariable v = entry.getKey();
                Rational r = entry.getValue();
                r = r.negate();
                goalFunction.put(v, r);
            }
            Rational constant = constraint.getConstant().negate();

            simbu.setGoalFunction(goalFunction);

            simbu.setIntegerProblem();

            sim = simbu.buildSimplexTable();

            result = sim.solve();

            if(result == null){
                // unsolvable
                // replace by contradiction 0 = 1
                LinearConstraint contradiction =
                    new LinearConstraint(new HashMap<AlgebraVariable, Integer>(),ConstraintType.EQUALITY,1);

                this.constraints.clear();
                this.inequations.clear();
                this.equations.clear();
                this.equations.add(contradiction);
                this.dissolvings.clear();

                return true;
            }

            if (!sim.isUnrestricted() && result.equals(constant)) {
                // the constraint is an implicit equality
                redundantConstraints.add(constraint);

                constraint = constraint.changeConstraintType(ConstraintType.EQUALITY);
                this.equations.add(constraint);
            }
        }

        this.constraints.removeAll(redundantConstraints);

        return !redundantConstraints.isEmpty();

    }

    /**
     * @return returns for which variables there are dissolvings
     */
    public Set<AlgebraVariable> getDissolvingsDomain(){
        HashSet<AlgebraVariable> vars = new HashSet<AlgebraVariable>(this.dissolvings.size());
        for (Dissolving diss : this.dissolvings) {
            AlgebraVariable var = diss.getVariable();
            vars.add(var);
        }
        return vars;
    }


    public boolean isInvertable(Set<AlgebraVariable> vars){
        this.gaussTransformation();

        Set<AlgebraVariable> dissvars = this.getDissolvingsDomain();

        if(!dissvars.containsAll(vars)){
            return false;
        }
        else{
            return true;
        }

    }

    /**
     * Performs a Gauss transformation.
     * Possibly simple contradictions are detected
     * which make the constraints unsatisfiable.
     * In this case false is returned
     *
     * @return false if contradictions are detected which make the constraints unsatisfiable.
     */
    private void gaussTransformation() {

        for (AlgebraVariable var : this.allVariables) {
            AlgebraVariable disVar = null;
            LinearConstraint disEquation = null;

            // get an equation to dissolve
            for (LinearConstraint constraint : this.equations) {
                Set<AlgebraVariable> usedVariablesbyConstraint = constraint
                        .getUsedVariables();
                if (usedVariablesbyConstraint.contains(var)) {
                    disVar = var;
                    disEquation = constraint;
                    break;
                }
            }

            if (disEquation == null) {
                // nothing found for this variable
                // continue with another
                continue;
            }

            Dissolving dissolving = disEquation.dissolveFor(disVar);

            int size;

            size = this.constraints.size();
            for (int i = 0; i < size; i++) {
                LinearConstraint constraint = this.constraints.get(i);
                constraint = constraint.applyDissolving(dissolving);
                this.constraints.set(i, constraint);
            }

            size = this.inequations.size();
            for (int i = 0; i < size; i++) {
                LinearConstraint constraint = this.inequations.get(i);
                constraint = constraint.applyDissolving(dissolving);
                this.inequations.set(i, constraint);
            }

            size = this.dissolvings.size();
            for (int i = 0; i < size; i++) {
                Dissolving diss = this.dissolvings.get(i);
                diss = diss.applyDissolving(dissolving);
                this.dissolvings.set(i, diss);
            }

            this.dissolvings.add(dissolving);

            // delte this constraint
            // because we have found an equivalent dissolving
            this.equations.remove(disEquation);

            size = this.equations.size();
            for (int i = 0; i < size; i++) {
                LinearConstraint constraint = this.equations.get(i);
                constraint = constraint.applyDissolving(dissolving);
                this.equations.set(i, constraint);
            }
        }
    }

    /**
     * Removes Tautologies like: 0 = 0, 0 <= |c|, 0 != c
     * But also detects contradictions like: 0 = c, 0 <= -|c|, 0 != 0
     *
     * @return false if contradictions have been detected.
     */
    private boolean removeTautologies(){

        ArrayList<LinearConstraint> tautologies;
        tautologies = new ArrayList<LinearConstraint>(this.equations.size());

        for (LinearConstraint equation : this.equations){
            if (equation.getUsedVariables().isEmpty()){
                // 0 = c
                if(!equation.getConstant().equals(Rational.zero)) {
                    // this is a contradiction
                    return false;
                }
                else{
                    // this is a tautology
                    tautologies.add(equation);
                }
            }
        }
        this.equations.removeAll(tautologies);

        tautologies = new ArrayList<LinearConstraint>(this.inequations.size());

        for (LinearConstraint inequation : this.inequations) {
            if (inequation.getUsedVariables().isEmpty()) {
                // it has the form 0 != c
                if (inequation.getConstant().equals(Rational.zero)) {
                    // this is a contradiction
                    return false;
                }
                else{
                    // this is a tautology
                    tautologies.add(inequation);
                }
            }
        }
        this.inequations.removeAll(tautologies);

        tautologies = new ArrayList<LinearConstraint>(this.constraints.size());

        for (LinearConstraint constraint : this.constraints) {
            if (constraint.getUsedVariables().isEmpty()) {
                // it has the form 0 <= c
                if (constraint.getConstant().compareTo(Rational.zero) < 0) {
                    // this is a contradiction
                    return false;
                }
                else {
                    // this is a tautology
                    tautologies.add(constraint);
                }
            }
        }
        this.constraints.removeAll(tautologies);

        return true;
    }

    /**
     * Transforms the constraint into <=, = or !=
     * But not >=, < or >.
     *
     * Every coefficient and the constant get integers
     *
     * @param constraint The LinearConstraint to transform.
     * @return The LinearConstraint with type <=, = or !=
     *          and each number is an integer.
     */
    public static LinearConstraint toIntegerNormalForm(LinearConstraint constraint){

        Rational constant = constraint.getConstant();

        // make all coefficients and the constant integer
        Map<AlgebraVariable, Rational> newCoeffs = constraint.getCoefficients();
        Set<Entry<AlgebraVariable, Rational>> newCoeffsEntrySet = newCoeffs.entrySet();

        for (Entry<AlgebraVariable, Rational> entry : newCoeffsEntrySet) {
            int d = entry.getValue().getDenominator();
            if (d != 1){
                Rational dr = new Rational(d);
                for (Entry<AlgebraVariable, Rational> entry2 : newCoeffsEntrySet) {
                    Rational r = entry2.getValue().times(dr);
                    entry2.setValue(r);
                }
                constant = constant.times(dr);
            }
        }
        int d = constant.getDenominator();
        if (d != 1){
            Rational dr = new Rational(d);
            for (Entry<AlgebraVariable, Rational> entry2 : newCoeffsEntrySet) {
                Rational r = entry2.getValue().times(dr);
                entry2.setValue(r);
            }
            constant = constant.times(dr);
        }

        constraint = new LinearConstraint(newCoeffs,constraint.getConstraintType(), constant);

        // cancel by the gcd of all coefficients and the constant
        constraint = constraint.cancel();


        ConstraintType constraintType = constraint.getConstraintType();

        if (constraintType == ConstraintType.GREATEREQ){
            return constraint.timesMinusOne();
        }
        else if (constraintType == ConstraintType.LESSEQ){
            return constraint;
        }
        else if (constraintType == ConstraintType.EQUALITY){
            return constraint;
        }
        else if (constraintType == ConstraintType.INEQUALITY){
            return constraint;
        }


        if (constraintType == ConstraintType.GREATER) {
            constraint = constraint.timesMinusOne();
            constraintType = ConstraintType.LESS;
        }

        if (constraintType == ConstraintType.LESS) {

            constant = constraint.getConstant();

            // make all coefficients integer
            newCoeffs = constraint.getCoefficients();
            newCoeffsEntrySet = newCoeffs.entrySet();

            for (Entry<AlgebraVariable, Rational> entry : newCoeffsEntrySet) {
                d = entry.getValue().getDenominator();
                if (d != 1){
                    Rational dr = new Rational(d);
                    for (Entry<AlgebraVariable, Rational> entry2 : newCoeffsEntrySet) {
                        Rational r = entry2.getValue().times(dr);
                        entry2.setValue(r);
                    }
                    constant = constant.times(dr);
                }
            }

            // cancel by the gcd of all coefficients
            Rational gcd = new Rational();

            for (Entry<AlgebraVariable, Rational> entry : newCoeffsEntrySet) {
                gcd = Rational.gcd(gcd, entry.getValue());
            }

            if (!gcd.equals(new Rational(1)) && !gcd.equals(Rational.zero)){
                constant = constant.divideBy(gcd);
                for (Entry<AlgebraVariable, Rational> entry : newCoeffsEntrySet) {
                    Rational r = entry.getValue().divideBy(gcd);
                    entry.setValue(r);
                }
            }

            // decrease the constant to the next integer

            d = constant.getDenominator();
            int n =  constant.getNumerator();
            int diff = n % d;
            if(diff==0)
            {
                diff = d;
            }

            constant = new Rational(n-diff, d);

            return new LinearConstraint(newCoeffs,
                    ConstraintType.LESSEQ,
                    constant);
        }
        else{
            throw new RuntimeException("There seem to be other types of constraints.");
        }

    }

    /**
     * Transforms all constraints, equations and inequations
     * to be in integer form and restricts the solution space
     */
    private boolean toInteger(){

        int consSize = this.inequations.size();
        for (int i = 0; i < consSize; i++) {
            LinearConstraint constraint = this.inequations.get(i);

            constraint = LinearIntegerConstraintSimplifier.toIntegerSyntactically(constraint);

            Map<AlgebraVariable, Rational> coeff = constraint.getCoefficients();

            if (coeff.size()==1 && constraint.getConstant().equals(Rational.zero)){
                // transform x != 0 to x >= 1
                LinearConstraint c = new LinearConstraint(coeff, ConstraintType.GREATEREQ, new Rational(1));
                this.constraints.add(c);
                this.inequations.remove(i);
                i--;
                consSize--;
            }
            else{
                this.inequations.set(i, constraint);
            }
        }

        consSize = this.constraints.size();
        for (int i = 0; i < consSize; i++) {
            LinearConstraint constraint = this.constraints.get(i);

            constraint = LinearIntegerConstraintSimplifier.toIntegerSyntactically(constraint);

            this.constraints.set(i, constraint);
        }

        consSize = this.equations.size();
        for (int i = 0; i < consSize; i++) {
            LinearConstraint constraint = this.equations.get(i);

            constraint = LinearIntegerConstraintSimplifier.toIntegerSyntactically(constraint);

            this.equations.set(i, constraint);
        }

        consSize = this.constraints.size();
        for (int i = 0; i < consSize; i++) {
            LinearConstraint constraint = this.constraints.get(i);

            constraint = this.toIntegerSemantically(constraint);

            this.constraints.set(i, constraint);
        }


        return this.removeTautologies();
    }

    /**
     * Transforms a constraint into integer form and
     * restricts the solution space using a semantical analysis
     * respecting all other constraints, too.
     * The constraint itself is not modified
     * instead a new LinearConstraint is returned
     *
     * @param constraint The constraint to transform.
     * @return A constraint as result of the transformation of constraint
     *          in integer form.
     */
    private LinearConstraint toIntegerSemantically(LinearConstraint constraint) {

        if(constraint.getConstraintType() != ConstraintType.LESSEQ){
            return constraint;
        }

        SimplexBuilder simbu = new SimplexBuilder(this.constraints);
        simbu.setGoalFunction(constraint.getCoefficients());
        simbu.setIntegerProblem();

        Simplex sim = simbu.buildSimplexTable();
        Rational result = sim.solve();

        if (sim.isSatisfiable() && !sim.isUnrestricted()
                    && result.compareTo(constraint.getConstant()) < 0) {
            return new LinearConstraint(constraint.getCoefficients(),
                    constraint.getConstraintType(), result);
        }

        return constraint;
    }

    /**
     * Transforms a constraint into integer form and
     * restricts the solution space using a syntactically analysis
     * only of the given constraint.
     * The constraint itself is not modified
     * instead a new LinearConstraint is returned
     *
     * @param constraint The constraint to transform.
     * @return A constraint as result of the transformation of constraint
     *          in integer form.
     */
    public static LinearConstraint toIntegerSyntactically(LinearConstraint constraint){

        constraint = LinearIntegerConstraintSimplifier.toIntegerNormalForm(constraint);

        ConstraintType ct = constraint.getConstraintType();

        Rational newConstant = constraint.getConstant();

        Map<AlgebraVariable, Rational> newCoeffs = constraint.getCoefficients();
        Set<Entry<AlgebraVariable, Rational>> newCoeffsEntrySet = newCoeffs.entrySet();

        // cancel by the gcd of all coefficients
        Rational gcd = new Rational();

        for (Entry<AlgebraVariable, Rational> entry : newCoeffsEntrySet) {
            gcd = Rational.gcd(gcd, entry.getValue());
        }

        if (!gcd.equals(new Rational(1)) && !gcd.equals(Rational.zero)){
            newConstant = newConstant.divideBy(gcd);
            for (Entry<AlgebraVariable, Rational> entry : newCoeffsEntrySet) {
                Rational r = entry.getValue().divideBy(gcd);
                entry.setValue(r);
            }
        }

        int d = newConstant.getDenominator();
        if(d != 1){
            if(ct == ConstraintType.INEQUALITY) {
                // this trivially holds
                // return 0 != 1
                return new LinearConstraint(
                        new LinkedHashMap<AlgebraVariable, Rational>(),
                        ConstraintType.INEQUALITY,
                        new Rational(1));
            }
            else if(ct == ConstraintType.EQUALITY){
                // this is unsatisfiable
                // return 0 = 1
                return new LinearConstraint(
                        new LinkedHashMap<AlgebraVariable, Rational>(),
                        ConstraintType.EQUALITY,
                        new Rational(1));
            }

            // decrease the constant to the next integer
            int n =  newConstant.getNumerator();
            int diff = n % d;

            newConstant = new Rational(n-diff, d);
        }

        if(ct.equals(ConstraintType.EQUALITY) || ct.equals(ConstraintType.INEQUALITY)){
            return new LinearConstraint(newCoeffs, ct, newConstant);
        }
        else{
            return new LinearConstraint(newCoeffs, ConstraintType.LESSEQ, newConstant);
        }
    }


    /**
     * Adds a constraint in form of a term.
     *
     * @param term
     *            The term representing the constraint to add.
     * @param laProgram Background information about the properties of LA
     */
    public void addConstraint(AlgebraTerm term, LAProgramProperties laProgram) {
        LinearTermNormalizer ltn = new LinearTermNormalizer(laProgram);
        term.apply(ltn);
        LinearConstraint c = ltn.getConstraint();
        this.addConstraint(c);
    }

    /**
     * Adds a constraint.
     *
     * @param constraint
     *            The constraint to add.
     */
    public void addConstraint(LinearConstraint constraint) {
        if (constraint == null) {
            return;
        }

        if (constraint.getConstraintType() == null) {
            return;
        }

        if(constraint.isInteger()){
            if (constraint.getConstraintType() == ConstraintType.EQUALITY) {
                this.equations.add(constraint.deepcopy());
            }
            else if (constraint.getConstraintType() == ConstraintType.INEQUALITY) {
                this.inequations.add(constraint.deepcopy());
            }
            else {
                this.constraints.add(constraint.deepcopy());
            }

            Set<AlgebraVariable> additionalVariables = constraint.getUsedVariables();

            additionalVariables.removeAll(this.allVariables);

            this.allVariables.addAll(additionalVariables);
        }
    }

    /**
     * @return Returns all constraints.
     */
    public ArrayList<LinearConstraint> getAllConstraints() {
        int size = this.constraints.size() + this.inequations.size() + this.equations.size();
        ArrayList<LinearConstraint> all = new ArrayList<LinearConstraint>(size);

        all.addAll(this.constraints);
        all.addAll(this.equations);
        all.addAll(this.inequations);

        return all;
    }

    /**
     * @return Returns the constraints of type <=.
     */
    public ArrayList<LinearConstraint> getConstraints() {
        return this.constraints;
    }

    /**
     * @return Returns the inequations
     */
    public ArrayList<LinearConstraint> getInequations() {
        return this.inequations;
    }

    /**
     * @return Returns the equations
     */
    public ArrayList<LinearConstraint> getEquations() {
        return this.equations;
    }

    private void constraintsToIntTransform(){
        int size = this.equations.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint equation = this.equations.get(i);

            LinearConstraint newEquation = equation.toInteger();
            this.equations.set(i, newEquation);
        }

        size = this.inequations.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint inequation = this.inequations.get(i);

            LinearConstraint newInequation = inequation.toInteger();
            this.inequations.set(i, newInequation);
        }

        size = this.constraints.size();
        for (int i = 0; i < size; i++) {
            LinearConstraint constraint = this.constraints.get(i);

            LinearConstraint newConstraint = constraint.toInteger();
            this.constraints.set(i, newConstraint);
        }
    }

    /**
     * Guarantees that there is no minus in a dissolving.
     * Even if it costs transforming dissolvings back to equations.
     */
    private void dissolvingsToPlusTransform(){

        int size = this.dissolvings.size();

        for (int i = 0; i < size; i++) {
            Dissolving dissolving = this.dissolvings.get(i);

            Map<AlgebraVariable, Rational> coeffs = dissolving.getCoefficients();
            Rational constant = dissolving.getConstant();

            // if there is an dissolving like x = n y + b z with a negative n
            // it gets an equation
            Set<Entry<AlgebraVariable, Rational>> entrySet = coeffs.entrySet();

            int negativeCount = 0;

            if(constant.compareTo(Rational.zero) < 0){
                negativeCount++;
            }
            else{
                for (Entry<AlgebraVariable, Rational> entry : entrySet) {
                    if(entry.getValue().getNumerator() < 0){
                        negativeCount++;
                        break;
                    }
                }
            }

            if(negativeCount == 0){
                // perfect nothing to do
                continue;
            }

            LinearConstraint eq = dissolving.toEquation();

            Map<AlgebraVariable, Rational> coeff = eq.getCoefficients();

            int positive = 0;
            int negative = 0;
            AlgebraVariable selectedPositive = null;
            AlgebraVariable selectedNegative = null;

            for (Entry<AlgebraVariable, Rational> entry : coeff.entrySet()) {
                if(entry.getValue().compareTo(Rational.zero) > 0){
                    positive++;
                    selectedPositive = entry.getKey();
                }
                else{
                    negative++;
                    selectedNegative = entry.getKey();
                }
            }

            Dissolving newDissolving = null;

            if(positive == 1 && negative == 1 && constant.equals(Rational.zero)){

                // special case: here there are two dissolving possible
                // the preferedVariables decide
                int posIndex = this.preferedVariables.lastIndexOf(selectedPositive);
                int negIndex = this.preferedVariables.lastIndexOf(selectedNegative);

                if(posIndex < negIndex){
                    newDissolving = eq.dissolveFor(selectedPositive);
                }
                else{
                    newDissolving = eq.dissolveFor(selectedNegative);
                }
            }
            else if(positive == 1 && constant.compareTo(Rational.zero) >= 0){
                newDissolving = eq.dissolveFor(selectedPositive);
            }
            else if(negative == 1 && constant.compareTo(Rational.zero) <= 0){
                newDissolving = eq.dissolveFor(selectedNegative);
            }

            if(newDissolving == null){
                // there is no fix
                this.equations.add(eq);
                this.dissolvings.remove(i);
                size--;
                i--;
            }
            else {
                this.dissolvings.set(i, newDissolving);

                this.applyDissolving(newDissolving);
            }

        }
    }

}
