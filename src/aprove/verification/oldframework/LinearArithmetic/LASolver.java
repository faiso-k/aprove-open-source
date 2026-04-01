package aprove.verification.oldframework.LinearArithmetic;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * A Solver for linear arithmetic problems.
 * (Linear (in)equalities over the integers >= 0)
 *
 * @author dickmeis
 * @version $Id$
 */

public class LASolver {

    // constraints with type <, >, >=, <=
    private ArrayList<LinearConstraint> constraints;

    // constraints with type =
    private ArrayList<LinearConstraint> equations;

    // constraints with type !=
    private ArrayList<LinearConstraint> inequations;

    private ArrayList<Dissolving> dissolvings;

    // the priority of a variable when an equation is dissolved
    // The first variable in the list has the highest priority.
    private List<AlgebraVariable> preferedVariables;

    /**
     * Constructor for a LASolver. The list preferedVariables
     * gives the priority of a variable when it comes to dissolve an equation
     * for a variable. The first variable in the list has the highest priority.
     *
     * @param preferedVariables
     *            List of variables indicating their priority when an equation
     *            is dissolved for a variable. The first variable in the list
     *            has the highest priority.
     */
    public LASolver(List<AlgebraVariable> preferedVariables){
        this.constraints = new ArrayList<LinearConstraint>();
        this.equations = new ArrayList<LinearConstraint>();
        this.inequations = new ArrayList<LinearConstraint>();
        this.dissolvings = new ArrayList<Dissolving>();

        this.preferedVariables = preferedVariables;
    }

    /**
     * Constructor for a LASolver.
     * There are not any prefered variables.
     */
    public LASolver(){
        this(new ArrayList<AlgebraVariable>());
    }

    /**
     * Constructor for a LASolver. The variables in the set preferedVariables
     * have priority when an equation is dissolved for a variable.
     * They have all the same priority.
     *
     * @param preferedVariables
     *            Set of variables having priority when an equation is dissolved for a variable.
     */
    public LASolver(Set<AlgebraVariable> preferedVariables) {
        this(new ArrayList<AlgebraVariable>(preferedVariables));
    }

    /**
     * @return Returns all constraints
     */
    public ArrayList<LinearConstraint> getAllConstraints() {
        ArrayList<LinearConstraint> allConstraints;
        allConstraints = new ArrayList<LinearConstraint>(this.constraints.size()
                + this.equations.size() + this.inequations.size());

        allConstraints.addAll(this.constraints);
        allConstraints.addAll(this.equations);
        allConstraints.addAll(this.inequations);

        return allConstraints;
    }


    /**
     * @return Returns the dissolvings.
     */
    public ArrayList<Dissolving> getDissolvings() {
        return this.dissolvings;
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

    /**
     * Solves a linear arithmetic problem.
     * Returns true iff the problem is satisfiable.
     * The dissolvings and the simplified constraints and equation
     * can then be obtained by the getter methods.
     *
     * @return true iff the problem is satisfiable.
     */
    public boolean solve(){

        LinearIntegerConstraintSimplifier lcs = new LinearIntegerConstraintSimplifier(this.preferedVariables, this.constraints);

        boolean satisfiable;

        // first simplify
        satisfiable = lcs.simplify();
        if (!satisfiable){
            return false;
        }

        this.dissolvings = lcs.getDissolvings();
        this.constraints = lcs.getConstraints();
        this.equations = lcs.getEquations();
        this.inequations = lcs.getInequations();

        // check for satisfyability
        // use simplex algorithm

        // but inequality restrictions are not convex
        // therefore split for each inequality into two convex problems

        ArrayList<ArrayList<LinearConstraint>> constraintSets = new ArrayList<ArrayList<LinearConstraint>>();
        ArrayList<LinearConstraint> convex = new ArrayList<LinearConstraint>();

        for (LinearConstraint constraint : this.constraints) {
            convex.add(constraint.deepcopy());
        }
        for (LinearConstraint constraint : this.equations) {
            convex.add(constraint.deepcopy());
        }
        for (Dissolving dis : this.dissolvings) {
            // it needs to be checked that the values are not negative
            convex.add(dis.toEquation());
        }

        if(!convex.isEmpty()){
            constraintSets.add(convex);
        }

        for (LinearConstraint ineq1: this.inequations) {
            LinearConstraint ineq2;

            ineq2 = ineq1.changeConstraintType(ConstraintType.LESS);
            ineq2 = LinearIntegerConstraintSimplifier.toIntegerSyntactically(ineq2);

            ineq1 = ineq1.changeConstraintType(ConstraintType.GREATER);
            ineq1 = LinearIntegerConstraintSimplifier.toIntegerSyntactically(ineq1);

            ArrayList<ArrayList<LinearConstraint>> newConstraintSets = new ArrayList<ArrayList<LinearConstraint>>();

            for (ArrayList<LinearConstraint> cs1: constraintSets) {
                ArrayList<LinearConstraint> cs2 = new ArrayList<LinearConstraint>();
                for (LinearConstraint constraint : cs1) {
                    LinearConstraint c = constraint.deepcopy();
                    cs2.add(c);
                }

                cs1.add(ineq1);
                cs2.add(ineq2);

                newConstraintSets.add(cs1);
                newConstraintSets.add(cs2);

            }

            constraintSets = newConstraintSets;
        }

        if (constraintSets.isEmpty()){
            return true;
        }

        satisfiable = false;

        for (ArrayList<LinearConstraint> cons : constraintSets) {

            SimplexBuilder simbuild = new SimplexBuilder(cons);
            simbuild.setIntegerProblem();

            Simplex simplex = simbuild.buildSimplexTable();

            simplex.solve();

            if(simplex.isSatisfiable()){
                satisfiable = true;
                break;
            }
        }

        if(satisfiable == false){
            return false;
        }

        return true;

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
        if (constraint != null) {
            if (constraint.getConstraintType() == null) {
                return;
            }

            this.constraints.add(constraint);
        }
    }

    /**
     * Adds all constraints contained in the list
     *
     * @param constraints a list of constraints to add
     */
    public void addAllConstraints(List<LinearConstraint> constraints) {
        for (LinearConstraint constraint : constraints) {
            this.addConstraint(constraint);
        }
    }

    /**
     * Adds a constraint in form of an equation
     *
     * @param equation The equation to add
     * @param laProgram Background information about the properties of LA
     */
    public void addConstraint(Equation equation, LAProgramProperties laProgram) {
        LinearConstraint constraint = LinearConstraint.create(equation, laProgram);
        this.addConstraint(constraint);
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

}
