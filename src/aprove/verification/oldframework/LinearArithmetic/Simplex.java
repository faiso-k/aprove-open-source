package aprove.verification.oldframework.LinearArithmetic;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;

/**
 * Implementation of the primal simplex algorithm
 * It is extended for integer problems by the gomory method.
 * Therefore there is the dual simplex algorithm, too.
 * (No guarantee that this works on its own.)
 *
 * The table is expected to be in normal form e.g. for m constraints there have
 * to be m unity vectors wich form the basis. These basis variables have to be
 * announced in the correct order.
 *
 * It is suggested that the simplex table is constructed by the SimplexBuilder
 * @see SimplexBuilder
 *
 * @author dickmeis
 * @version $Id$
 */

public class Simplex {

    private static final boolean DEBUB_SIMPLEX = Globals.DEBUG_DICKMEIS && false;

    // the lhs of the constraints with size m*n
    private Rational[][] table;

    private int m;

    private int n;

    // the rhs of the constraints with size m
    private Rational[] bColumn;

    // size n
    private Rational[] goalFunction;

    // size n
    private Rational[] deltaZ;

    // the indizes of the variables in the basis (size m)
    private int[] basisVariables;

    private Rational goalFunctionValue;

    // indicates whether a further primal optimization step has to be done
    // iff is not primal adhessible
    private boolean nextPrimalStepPossible = false;

    // indicates whether a further dual optimization step has to be done
    // iff is not dual adhessible
    private boolean nextDualStepPossible = false;

    // indicates iff the search space is unrestricted
    // and therefore the optimum does not exsist
    private boolean unrestricted = false;

    // indicates iff the search space is non-empty
    private boolean satisfiable = true;

    // the variables that must satisfy integer restrictions
    public Set<Integer> integerVariables;

    /**
     * Constructs a simplex table.
     * The table is expected to be in normal form e.g. for m constraints there have
     * to be m unity vectors wich form the basis. These basis variables have to be
     * announced in the correct order.
     *
     * @param goalFunction
     * @param table in normal form
     * @param bColumn
     * @param basisVariables
     * @param integerVariables the variables that must satisfy integer restrictions
     */
    public Simplex(Rational goalFunction[], Rational table[][],
            Rational bColumn[], int basisVariables[],
            Set<Integer> integerVariables) {
        this.goalFunction = goalFunction;
        this.table = table;
        this.bColumn = bColumn;
        this.basisVariables = basisVariables;
        this.m = table.length;
        this.n = table[0].length;
        this.deltaZ = new Rational[this.n];

        if(integerVariables==null){
            this.integerVariables = new HashSet<Integer>();
        }
        else{
            this.integerVariables = integerVariables;
        }
    }

    /**
     * Constructs a simplex table.
     * The table is expected to be in normal form e.g. for m constraints there have
     * to be m unity vectors wich form the basis. These basis variables have to be
     * announced in the correct order.
     *
     * @param goalFunction
     * @param table in normal form
     * @param bColumn
     * @param basisVariables
     */
    public Simplex(Rational goalFunction[], Rational table[][],
            Rational bColumn[], int basisVariables[]) {
        this(goalFunction, table, bColumn, basisVariables, null);
    }

    /**
     * Solves the given maximization problem.
     * Returns the optimum if it exsists.
     * Before you use it check if the search space is not empty
     * or unrestricted
     *
     * @return the maximum value if it exsists.
     */
    public Rational solve() {
        try {
            this.calculateDeltaZ();
            this.calculateGoalFunctionValue();

            if (Simplex.DEBUB_SIMPLEX) {
                System.out.println(this);
            }

            while (this.nextPrimalStepPossible) {
                this.nextPrimalStepPossible = false;

                this.primalStep();

                if (Simplex.DEBUB_SIMPLEX) {
                    System.out.println("\n\n\n");
                    System.out.println(this);
                }
            }

            this.gomory();

            return this.goalFunctionValue;
        }
        catch (Exception e) {
            System.err.println("Error in simplex algorithm.\n");
            e.printStackTrace();
        }
        return null;
    }

    /**
     * Inserts a gomory restriction into the table.
     */
    private void gomory() {

        // cycle till all integer restrictions are fullfilled
        // or it is determined that the seach space is empty
        while (this.satisfiable) {

            int argmax = 0;
            Rational max = null;

            /*
             * select a variable which does not fullfill the integer
             * restricition
             */
            for (int i = 0; i < this.m; i++) {
                if (this.integerVariables.contains(this.basisVariables[i])
                        && this.bColumn[i].getDenominator() != 1) {
                    // a variable which should be integer but isn't
                    Rational r = this.bColumn[i].getRationalPart();
                    if (max == null || r.compareTo(max) > 0) {
                        argmax = i;
                        max = r;
                    }
                }
            }

            if (max == null) {
                // all integer restrictions are fullfilled
                return;
            }
            int t = argmax;

            /*
             * insert a gomory restriction. copy therefore the table
             */
            Rational newGoalFunction[] = new Rational[this.n + 1];
            for (int j = 0; j < this.n; j++) {
                newGoalFunction[j] = this.goalFunction[j].deepcopy();
            }
            newGoalFunction[this.n] = new Rational();

            Rational newTable[][] = new Rational[this.m + 1][this.n + 1];
            for (int i = 0; i < this.m; i++) {
                for (int j = 0; j < this.n; j++) {
                    newTable[i][j] = this.table[i][j].deepcopy();
                }
                newTable[i][this.n] = new Rational();
            }
            for (int j = 0; j < this.n; j++) {
                newTable[this.m][j] = this.table[t][j].getRationalPart().negate();
            }
            newTable[this.m][this.n] = new Rational(1);

            Rational newBColumn[] = new Rational[this.m + 1];
            for (int i = 0; i < this.m; i++) {
                newBColumn[i] = this.bColumn[i].deepcopy();
            }
            newBColumn[this.m] = this.bColumn[t].getRationalPart().negate();

            int newBasisVariables[] = new int[this.m + 1];
            for (int i = 0; i < this.m; i++) {
                newBasisVariables[i] = this.basisVariables[i];
            }
            newBasisVariables[this.m] = this.n;

            Rational newDeltaZ[] = new Rational[this.n + 1];
            for (int j = 0; j < this.n; j++) {
                newDeltaZ[j] = this.deltaZ[j].deepcopy();
            }
            newDeltaZ[this.n] = new Rational();

            this.m++;
            this.n++;
            this.goalFunction = newGoalFunction;
            this.table = newTable;
            this.bColumn = newBColumn;
            this.basisVariables = newBasisVariables;
            this.deltaZ = newDeltaZ;

            this.nextDualStepPossible = true;

            this.dualSolve();
        }
    }

    private Rational dualSolve() {
        try {
            if (Simplex.DEBUB_SIMPLEX) {
                System.out.println(this);
            }

            while (this.nextDualStepPossible) {
                this.nextDualStepPossible = false;

                this.dualStep();

                if (Simplex.DEBUB_SIMPLEX) {
                    System.out.println("\n\n\n");
                    System.out.println(this);
                }
            }

            return this.goalFunctionValue;
        }
        catch (Exception e) {
            System.err.println("Error in simplex algorithm.\n");
            e.printStackTrace();
        }

        return null;
    }

    /**
     * Initialize the goal function value. By the optimization steps the goal
     * function value will be updated This saves some calculation steps
     */
    private void calculateGoalFunctionValue() {
        this.goalFunctionValue = new Rational();
        for (int i = 0; i < this.m; i++) {
            Rational basicGoalValue = this.goalFunction[this.basisVariables[i]];
            Rational temp = this.bColumn[i].times(basicGoalValue);
            this.goalFunctionValue = this.goalFunctionValue.plus(temp);
        }
    }

    /**
     * Initialize the delta z. By the optimization delta z will be updated. This
     * saves some calculation steps
     */
    private void calculateDeltaZ() {
        for (int j = 0; j < this.n; j++) {
            this.deltaZ[j] = this.goalFunction[j].negate();
            for (int i = 0; i < this.m; i++) {
                Rational temp = this.goalFunction[this.basisVariables[i]];
                temp = temp.times(this.table[i][j]);
                this.deltaZ[j] = this.deltaZ[j].plus(temp);
            }

            // check for primal permissibility (german: primale Zul?ssigkeit)
            // if not a optimization step has to be done
            if (this.nextPrimalStepPossible == false
                    && this.deltaZ[j].compareTo(Rational.zero) < 0) {
                this.nextPrimalStepPossible = true;
            }
        }
    }

    /**
     * Select the pivot column
     *
     * @return the pivot column
     */
    private int selectPivotColumn() {
        int argmin = 0;
        Rational min = this.deltaZ[0];

        for (int j = 1; j < this.n; j++) {
            if (this.deltaZ[j].compareTo(Rational.zero) < 0
                    && this.deltaZ[j].compareTo(min) < 0) {
                argmin = j;
                min = this.deltaZ[j];
            }
        }

        return argmin;
    }

    /**
     * Select the pivot row in the given pivot column
     * By that the pivot element is determined.
     *
     * @param pivotColumn
     *            The column where to search the pivot element.
     * @return the pivot row. null iff none was found.
     */
    private Integer selectPivotRow(int pivotColumn) {
        Integer argmin = null;
        Rational min = null;

        for (int i = 0; i < this.m; i++) {
            if (this.table[i][pivotColumn].compareTo(Rational.zero) > 0) {
                Rational temp = this.bColumn[i].divideBy(this.table[i][pivotColumn]);

                if (Simplex.DEBUB_SIMPLEX) {
                    System.out.println(temp);
                }

                if (min == null || temp.compareTo(min) < 0) {
                    argmin = i;
                    min = temp;
                }
            }
            else if (Simplex.DEBUB_SIMPLEX) {
                System.out.println("-");
            }
        }

        return argmin;
    }

    /**
     * Do a optimization step. Update the table. At the same time update the
     * delta z and the goal function value and determine if another step is
     * possible.
     */
    private void primalStep() {
        int l = this.selectPivotColumn();
        Integer row = this.selectPivotRow(l);
        int k = 0;
        if (row != null) {
            k = row;
        }
        else {
            // there is no pivot element
            this.nextPrimalStepPossible = false;
            this.unrestricted = true;
            return;
        }

        if (Simplex.DEBUB_SIMPLEX) {
            System.out.println("col: " + l + "  row: " + k);
        }

        this.exchange(k, l);
    }

    private void exchange(int row, int col) {
        Rational[][] newTable = new Rational[this.m][this.n];
        Rational[] newBColumn = new Rational[this.m];
        Rational[] newDeltaZ = new Rational[this.n];

        // refresh
        for (int j = 0; j < this.n; j++) {

            if (j != col) {

                Rational temp = this.table[row][j].divideBy(this.table[row][col]);
                Rational temp2;

                for (int i = 0; i < this.m; i++) {
                    // refresh table

                    if (i == row) {
                        newTable[i][j] = this.table[i][j].divideBy(this.table[row][col]);
                    }
                    else {
                        temp2 = temp.times(this.table[i][col]);
                        newTable[i][j] = this.table[i][j].minus(temp2);
                    }
                }

                // refresh deltaZ
                temp2 = temp.times(this.deltaZ[col]);
                newDeltaZ[j] = this.deltaZ[j].minus(temp2);

                // check for primal permissibility (german: primale
                // Zulaessigkeit)
                // if not a optimization step has to be done
                if (this.nextPrimalStepPossible == false
                        && newDeltaZ[j].compareTo(Rational.zero) < 0) {
                    this.nextPrimalStepPossible = true;
                }
            }
            else {
                for (int i = 0; i < this.m; i++) {
                    // refresh table
                    if (i == row) {
                        newTable[i][j] = new Rational(1);
                    }
                    else {
                        newTable[i][j] = new Rational();
                    }
                }

                // refresh delta z
                newDeltaZ[j] = new Rational();
            }

        }

        Rational temp = this.bColumn[row].divideBy(this.table[row][col]);
        Rational temp2;

        // refresh b column
        for (int i = 0; i < this.m; i++) {
            if (i == row) {
                newBColumn[i] = temp;
            }
            else {
                temp2 = temp.times(this.table[i][col]);
                newBColumn[i] = this.bColumn[i].minus(temp2);
            }

            // check for dual permissibility (german: duale
            // Zulaessigkeit)
            // if not a optimization step has to be done
            if (this.nextDualStepPossible == false
                    && newBColumn[i].compareTo(Rational.zero) < 0) {
                this.nextDualStepPossible = true;
            }
        }

        temp2 = temp.times(this.deltaZ[col]);
        this.goalFunctionValue = this.goalFunctionValue.minus(temp2);

        this.table = newTable;
        this.deltaZ = newDeltaZ;
        this.bColumn = newBColumn;

        // set new variable in the basis
        this.basisVariables[row] = col;
    }

    /**
     * performs a dual optimization step
     */
    private void dualStep() {
        int k = this.selectDualPivotRow();
        Integer column = this.selectDualPivotColumn(k);

        int l = 0;
        if (column != null) {
            l = column;
        }
        else {
            // there is no pivot element
            this.nextDualStepPossible = false;
            this.goalFunctionValue = null;
            this.satisfiable = false;
            return;
        }

        if (Simplex.DEBUB_SIMPLEX) {
            System.out.println("col: " + l + "  row: " + k);
        }

        this.exchange(k, l);
    }

    /**
     * Select the pivot column in the given pivot row.
     * By that the pivot element is determined.
     *
     * @param pivotRow
     *            The row where to search the pivot element.
     * @return the pivot column. null iff none was found.
     */
    private Integer selectDualPivotColumn(int pivotRow) {
        Integer argmin = null;
        Rational max = null;

        for (int j = 0; j < this.n; j++) {
            if (this.table[pivotRow][j].compareTo(Rational.zero) < 0) {
                Rational temp = this.deltaZ[j].divideBy(this.table[pivotRow][j]);

                if (Simplex.DEBUB_SIMPLEX) {
                    System.out.println(temp);
                }

                if (max == null || temp.compareTo(max) > 0) {
                    argmin = j;
                    max = temp;
                }
            }
            else if (Simplex.DEBUB_SIMPLEX) {
                System.out.println("-");
            }
        }

        return argmin;
    }

    /**
     * Select the pivot row for a dual optimization step
     *
     * @return the pivot row
     */
    private int selectDualPivotRow() {
        int argmin = 0;
        Rational min = this.bColumn[0];

        for (int i = 1; i < this.m; i++) {
            if (this.bColumn[i].compareTo(Rational.zero) < 0
                    && this.bColumn[i].compareTo(min) < 0) {
                argmin = i;
                min = this.deltaZ[i];
            }
        }

        return argmin;
    }

    /**
     * prints the simplex tabel use only for debugging
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("\t\t  ");
        for (Rational r : this.goalFunction) {
            sb.append(r + " \t");
        }
        sb.append("\n");

        for (int i = 0; i < this.m; i++) {
            int index = this.basisVariables[i];

            sb.append(index + "\t| ");
            sb.append(this.goalFunction[index] + "\t| ");

            for (int j = 0; j < this.n; j++) {
                sb.append(this.table[i][j] + " \t");
            }

            sb.append("|  " + this.bColumn[i] + "\n");
        }

        sb.append("\t\t  ");
        for (Rational r : this.deltaZ) {
            if (r != null) {
                sb.append(r + " \t");
            }
            else {
                sb.append(" \t");
            }
        }
        sb.append("|  " + this.goalFunctionValue);
        sb.append("\n");

        return sb.toString();
    }

    /**
     * Indicates iff the search space is non-empty
     *
     * @return true iff the search space is non-empty
     */
    public boolean isSatisfiable(){
        return this.satisfiable && !this.goalFunctionValue.isM();
    }

    /**
     * indicates iff the search space is unrestricted
     * and therefore the optimum does not exsist
     *
     * @return true iff the search space is unrestricted
     */
    public boolean isUnrestricted(){
        return this.unrestricted;
    }

}
