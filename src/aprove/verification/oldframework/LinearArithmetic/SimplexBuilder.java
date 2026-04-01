package aprove.verification.oldframework.LinearArithmetic;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Builds up the simplex table.
 *
 * First add the constraints and set up the goal function.
 * Then build the table.
 *
 * @author dickmeis
 */

public class SimplexBuilder {

    private static final boolean DEBUG = Globals.DEBUG_DICKMEIS && false;

    private final ArrayList<LinearConstraint> constraints;

    private final List<AlgebraVariable> usedVariables;

    private Map<AlgebraVariable, Rational> goalFunctionVariables;

    private Rational table[][];
    private Rational bColumn[];
    private int basisVariables[];
    private int m, n;

    private Set<Integer> integerVariables;

    private final List<AlgebraVariable> inputVariables;

    /**
     * Constructs a SimplexBuilder
     */
    public SimplexBuilder() {
        this.constraints = new ArrayList<LinearConstraint>();
        this.usedVariables = new ArrayList<AlgebraVariable>();
        this.inputVariables = new ArrayList<AlgebraVariable>();
        this.goalFunctionVariables = new LinkedHashMap<AlgebraVariable, Rational>();
        this.integerVariables = null;
    }

    /**
     * Constructs a SimplexBuilder with some initial constraints.
     *
     * @param constraints the initial constraints
     */
    public SimplexBuilder(final Collection<LinearConstraint> constraints) {
        this.usedVariables = new ArrayList<AlgebraVariable>();
        this.inputVariables = new ArrayList<AlgebraVariable>();

        this.constraints = new ArrayList<LinearConstraint>(constraints.size());
        for (final LinearConstraint constraint : constraints) {
            this.addConstraint(constraint);
        }

        this.goalFunctionVariables = new LinkedHashMap<AlgebraVariable, Rational>();
        this.integerVariables = null;
    }

    /**
     * Set the varaibles which have to satisfy integer restrictions
     *
     * @param integerVariables variables having to satisfy integer restrictions
     */
    public void setIntegerVariables(final Collection<AlgebraVariable> integerVariables) {
        this.integerVariables = new HashSet<Integer>(integerVariables.size());
        for (final AlgebraVariable variable : integerVariables) {
            int i = this.usedVariables.indexOf(variable);
            if (i == -1) {
                // not found
                this.usedVariables.add(variable);
                i = this.usedVariables.size() - 1;
            }
            this.integerVariables.add(i);
        }
    }

    /**
     * Set all variables (but the slackness or penalty variables)
     * to satisfy integer restrictions
     */
    public void setIntegerProblem() {
        this.setIntegerVariables(this.inputVariables);
    }

    /**
     * List of the used variables in the same order
     * in which they are listed in the simplex table.
     *
     * @return a list of all used variables
     */
    public List<AlgebraVariable> getUsedVariables() {
        return this.usedVariables;
    }

    /**
     * Sets the goal function which is represented
     * by a mapping of a variable to its coefficient.
     *
     * @param goalFunction
     */
    public void setGoalFunction(final Map<AlgebraVariable, Rational> goalFunction) {
        this.goalFunctionVariables = new LinkedHashMap<AlgebraVariable, Rational>();
        for (final Entry<AlgebraVariable, Rational> entry : goalFunction.entrySet()) {
            final AlgebraVariable v = entry.getKey();
            this.goalFunctionVariables.put(v, entry.getValue());
            if (!this.usedVariables.contains(v)) {
                this.usedVariables.add(v);
            }
        }
    }

    /**
     * Adds a constraint.
     *
     * @param constraint The constraint to add.
     */
    public void addConstraint(final LinearConstraint constraint) {
        if (constraint != null) {
            if (constraint.getConstraintType() == null) {
                return;
            }

            if (constraint.getConstraintType() == ConstraintType.GREATER) {
                System.err.println("Unable to deal with > because it is not closed.");
                return;
            } else if (constraint.getConstraintType() == ConstraintType.LESS) {
                System.err.println("Unable to deal with < because it is not closed.");
                return;
            } else if (constraint.getConstraintType() == ConstraintType.INEQUALITY) {
                System.err.println("Unable to deal with != because it is not convex");
                return;
            }

            this.constraints.add(constraint.deepcopy());

            for (final Entry<AlgebraVariable, Rational> entry : constraint.getCoefficients().entrySet()) {
                final AlgebraVariable v = entry.getKey();
                if (!this.usedVariables.contains(v)) {
                    this.usedVariables.add(v);
                    this.inputVariables.add(v);
                }
            }
        }
    }

    /**
     * Builds the simplex table from the constraints.
     * The constraints are therefore transformed into the normal form.
     *
     * Therefore you have to add all constraints and set up the goal function
     * before you call this method.
     *
     * @return
     */
    public Simplex buildSimplexTable() {

        this.m = this.constraints.size();
        this.basisVariables = new int[this.m];

        // to normal form

        int basisVarIndex = this.usedVariables.size();

        final FreshVarGenerator fvg = new FreshVarGenerator(this.usedVariables);

        for (int i = 0; i < this.m; i++) {
            LinearConstraint constraint = this.constraints.get(i);

            // if b < 0 multiply with -1
            if (constraint.getConstant().compareTo(Rational.zero) < 0) {
                constraint = constraint.timesMinusOne();
                this.constraints.set(i, constraint);
            }

            if (constraint.getConstraintType() == ConstraintType.LESSEQ) {
                // add a slack variable which is a basis variable
                final VariableSymbol vss = VariableSymbol.create("S");
                final AlgebraVariable vs = AlgebraVariable.create(vss);
                final AlgebraVariable vsN = fvg.getFreshVariable(vs, false);

                final Map<AlgebraVariable, Rational> coeffs = constraint.getCoefficients();
                coeffs.put(vsN, new Rational(1));
                this.usedVariables.add(vsN);

                constraint = new LinearConstraint(coeffs, ConstraintType.EQUALITY, constraint.getConstant());
                this.constraints.set(i, constraint);

                this.basisVariables[i] = basisVarIndex;
                basisVarIndex++;
            } else if (constraint.getConstraintType() == ConstraintType.GREATEREQ) {
                // add a slack variable which is not a basis variable
                final VariableSymbol vss = VariableSymbol.create("S");
                final AlgebraVariable vs = AlgebraVariable.create(vss);
                final AlgebraVariable vsN = fvg.getFreshVariable(vs, false);

                final Map<AlgebraVariable, Rational> coeffs = constraint.getCoefficients();
                coeffs.put(vsN, new Rational(-1));
                this.usedVariables.add(vsN);

                // not a basis variable
                basisVarIndex++;

                // add a penalty variable
                final VariableSymbol vts = VariableSymbol.create("T");
                final AlgebraVariable vt = AlgebraVariable.create(vts);
                final AlgebraVariable vtN = fvg.getFreshVariable(vt, false);

                coeffs.put(vtN, new Rational(1));
                this.usedVariables.add(vtN);

                constraint = new LinearConstraint(coeffs, ConstraintType.EQUALITY, constraint.getConstant());
                this.constraints.set(i, constraint);

                this.goalFunctionVariables.put(vtN, Rational.createMinusM());
                this.basisVariables[i] = basisVarIndex;
                basisVarIndex++;
            } else if (constraint.getConstraintType() == ConstraintType.EQUALITY) {
                // add a penalty variable which is a basis variable
                final VariableSymbol vts = VariableSymbol.create("T");
                final AlgebraVariable vt = AlgebraVariable.create(vts);
                final AlgebraVariable vtN = fvg.getFreshVariable(vt, false);

                final Map<AlgebraVariable, Rational> coeffs = constraint.getCoefficients();
                coeffs.put(vtN, new Rational(1));
                this.usedVariables.add(vtN);

                constraint = new LinearConstraint(coeffs, ConstraintType.EQUALITY, constraint.getConstant());
                this.constraints.set(i, constraint);

                this.goalFunctionVariables.put(vtN, Rational.createMinusM());
                this.basisVariables[i] = basisVarIndex;
                basisVarIndex++;
            }

        }

        // build table

        this.n = this.usedVariables.size();

        final Rational goalFunction[] = new Rational[this.n];

        this.table = new Rational[this.m][this.n];
        this.bColumn = new Rational[this.m];

        for (int j = 0; j < this.n; j++) {
            final AlgebraVariable v = this.usedVariables.get(j);
            Rational r = this.goalFunctionVariables.get(v);
            if (r != null) {
                goalFunction[j] = r;
            } else {
                r = new Rational();
                goalFunction[j] = r;
                this.goalFunctionVariables.put(v, r);
            }
        }

        for (int i = 0; i < this.m; i++) {
            final LinearConstraint c = this.constraints.get(i);
            final Map<AlgebraVariable, Rational> coef = c.getCoefficients();

            for (int j = 0; j < this.n; j++) {
                final AlgebraVariable v = this.usedVariables.get(j);
                final Rational r = coef.get(v);

                if (r != null) {
                    this.table[i][j] = r;
                } else {
                    this.table[i][j] = new Rational();
                }
            }

            final Rational b = c.getConstant();
            this.bColumn[i] = b;
        }

        if (SimplexBuilder.DEBUG && Globals.DEBUG_DICKMEIS) {
            System.out.println(this.usedVariables);
        }

        return new Simplex(goalFunction, this.table, this.bColumn, this.basisVariables, this.integerVariables);
    }

}
