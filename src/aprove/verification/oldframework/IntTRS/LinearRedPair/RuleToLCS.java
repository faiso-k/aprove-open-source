package aprove.verification.oldframework.IntTRS.LinearRedPair;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.PolynomialConstraint.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Converts a rule into a system of linear constraints,
 * which is stored in the form
 * (A;A') (x,x') <= b  (of course component-by-component)
 * for some suitable A,  b. Here (x, x') denotes the vector
 * obtained by concatenation of x and x', i.e. x' is below x,
 * while (A;A') is the matrix where A is left part and A' is the right part.
 *
 * The translation will only work if the input rule has the format
 * f(x_1, ..., x_n) -> g(y_1, ..., y_n) | phi
 * where in phi only the variables x_i, y_j for i,j = 1, ..., n occur.
 *
 * @author Matthias Hoelzel
 *
 */
public class RuleToLCS {
    /** Rule to be translated */
    private final IGeneralizedRule rule;

    /** The resulting LCS */
    private LCS resultLCS;

    /** Left columns */
    private final LinkedHashMap<TRSVariable, Integer> leftColumns;

    /** Count the current number */
    private int leftColumnCounter;

    /** Right columns */
    private final LinkedHashMap<TRSVariable, Integer> rightColumns;

    /** Stores the constraints */
    private final LinkedList<LinkedHashMap<TRSVariable, BigInteger>> constraints;

    /** Stores the constant coefficient */
    private final LinkedList<BigInteger> constants;

    /** Count the current number */
    private int rightColumnCounter;

    /** Generates new names */
    private final FreshNameGenerator ng;

    private final Abortion aborter;

    /**
     * Incredible! It is a constructor!!
     * @param toTranslate rule to be translated
     * @param gen a name generator
     */
    public RuleToLCS(final IGeneralizedRule toTranslate, final FreshNameGenerator gen, final Abortion aborterParam) {
        this.aborter = aborterParam;
        this.rule = toTranslate;
        this.leftColumns = new LinkedHashMap<TRSVariable, Integer>(
                this.rule.getLeft().getArguments().size());
        this.rightColumns = new LinkedHashMap<TRSVariable, Integer>(
                ((TRSFunctionApplication) this.rule.getRight()).getArguments().size());
        this.ng = gen;
        this.constants = new LinkedList<BigInteger>();
        this.constraints = new LinkedList<LinkedHashMap<TRSVariable, BigInteger>>();
    }

    /**
     * Translates a rule.
     * @return the result LCS
     * @throws AbortionException
     */
    public LCS translate() throws AbortionException {
        if (this.resultLCS != null) {
            return this.resultLCS;
        }

        this.registerVariables();
        this.registerConstraints();
        this.buildMatrices();

        return this.resultLCS;
    }

    /**
     * Finds and register all variables.
     */
    private void registerVariables() {
        final Set<TRSVariable> leftVars = this.rule.getLeft().getVariables();
        final Set<TRSVariable> rightVars = this.rule.getRight().getVariables();

        if (Globals.DEBUG_MATTHIAS) {
            assert leftVars.size()
                == this.rule.getLeft().getRootSymbol().getArity()
                    : "Term should be linear!";
            assert rightVars.size()
                == ((TRSFunctionApplication) this.rule.getRight()).getRootSymbol().getArity()
                    : "Term should be linear!";
            for (final TRSVariable v : leftVars) {
                assert !rightVars.contains(v) : "Invalid rule detected: Bad variable: " + v;
            }
        }

        // Iterate over all the set of variables and register the variables:
        for (final TRSVariable leftVar : leftVars) {
            this.registerVariable(leftVar, true);
        }

        for (final TRSVariable rightVar : rightVars) {
            this.registerVariable(rightVar, false);
        }
    }

    /**
     * Registers a variable and assigns a column.
     * @param v variable to be registered
     * @param leftVariable boolean, true iff the variable occurs at the left side
     */
    private void registerVariable(final TRSVariable v, final boolean leftVariable) {
        // Left or right? -> Get the correct map:
        final LinkedHashMap<TRSVariable, Integer> map =
                leftVariable ? this.leftColumns : this.rightColumns;

        // Assign some column:
        int nextColumn;
        if (leftVariable) {
            nextColumn = this.leftColumnCounter;
            this.leftColumnCounter++;
        } else {
            nextColumn = this.rightColumnCounter;
            this.rightColumnCounter++;
        }

        map.put(v, nextColumn);
    }

    /**
     * Register the constraints.
     * @throws AbortionException
     */
    private void registerConstraints() throws AbortionException {
        // Get the constraints and register them:
        final List<PolynomialConstraint> polyConstraints =
            ToolBox.boolTermToPolynomialConstraints((TRSFunctionApplication) this.rule.getCondTerm(), this.ng,
                this.aborter);
        for (final PolynomialConstraint pc : polyConstraints) {
            this.registerConstraint(pc);
        }

        // To avoid empty matrices, we add a trivial constraint 0 <= 0, iff
        // we could not use any other constraints:
        if (this.constraints.size() == 0) {
            this.registerConstraint(new PolynomialConstraint(
                    VarPolynomial.create(0), PolynomialConstraintType.PCT_GE, this.ng));
        }
    }

    /**
     * Registers a constraint.
     * @param pc constraint to register
     */
    private void registerConstraint(final PolynomialConstraint pc) {
        final VarPolynomial vp = pc.getPolynomial();

        // We can only use constraints of the form t <= 0 for some polynomial t
        switch (pc.getType()) {
        case PCT_EQ:
            // t == 0 is equivalent to t >= 0 && t <= 0
            this.registerConstraint(
                    new PolynomialConstraint(vp, PolynomialConstraintType.PCT_GE, this.ng));
            this.registerConstraint(
                    new PolynomialConstraint(vp, PolynomialConstraintType.PCT_LE, this.ng));
            break;
        case PCT_GE:
            // t >= 0 is equivalent to -t <= 0
            this.registerConstraint(
                    new PolynomialConstraint(
                            vp.negate(),
                            PolynomialConstraintType.PCT_LE, this.ng));
            break;
        case PCT_LE:
            assert vp.isConcrete() : "Constraints should be concrete!";
            if (vp.getDegree() <= 1) {
                final BigInteger c = vp.getConstantPart().getNumericalAddend();
                this.constants.add(c.negate());

                final Set<String> variables = vp.getVariables();
                final LinkedHashMap<TRSVariable, BigInteger> constraint = new LinkedHashMap<TRSVariable, BigInteger>(variables.size());
                for (final String s : variables) {
                    final TRSVariable v = TRSTerm.createVariable(s);
                    final SimplePolynomial sp = vp.getCoefficientPoly(s);
                    assert sp.isConstant();
                    final BigInteger val = sp.getNumericalAddend();
                    constraint.put(v, val);
                }
                this.constraints.add(constraint);
            }
            break;
        default:
            // The types PCT_LT, PCT_GT can not occur since we used the method
            // ToolBox.boolTermToPolynomialConstraints to generate the constraints.
            // This method
            assert false : "Default?!?";
        }
    }

    /**
     * In this step we build the matrices for the LCS.
     */
    private void buildMatrices() {
        final int n = this.constraints.size();

        assert this.constants.size() == n
              : "Number of constants should be equal to the number of constraints";

        final VarPolynomial[][] arrA = new VarPolynomial[n][this.leftColumnCounter];
        final VarPolynomial[][] arrAPrime = new VarPolynomial[n][this.rightColumnCounter];
        final VarPolynomial[][] b = new VarPolynomial[n][1];

        int current = 0;

        final Iterator<LinkedHashMap<TRSVariable, BigInteger>> constraintsIter = this.constraints.iterator();
        final Iterator<BigInteger> constantsIter = this.constants.iterator();

        while (current < n) {
            // Note, that current is also used to iterator over the rows
            // of the matrices A and A' we are going to create.
            final BigInteger currentConstant = constantsIter.next();
            // Of course, constant parts are put into the b
            b[current][0] = VarPolynomial.create(currentConstant);

            final LinkedHashMap<TRSVariable, BigInteger> currentConstraint = constraintsIter.next();
            for (final Entry<TRSVariable, BigInteger> e : currentConstraint.entrySet()) {
                // Each variable belongs to the right or to the left side.
                // No variable belongs to boths side!!
                final TRSVariable v = e.getKey();
                final BigInteger val = e.getValue();
                // Put the right coefficient into the right matrix:
                if (this.leftColumns.containsKey(v)) {
                    final int pos = this.leftColumns.get(v);
                    arrA[current][pos] = VarPolynomial.create(val);
                } else if (this.rightColumns.containsKey(v)) {
                    final int pos = this.rightColumns.get(v);
                    arrAPrime[current][pos] = VarPolynomial.create(val);
                }
            }

            current++;
        }

        // Since the Matrix-class does not like null-value,
        // we better set unused values to ZERO manually:
        for (int i = 0; i < arrA.length; i++) {
            for (int j = 0; j < arrA[i].length; j++) {
                if (arrA[i][j] == null) {
                    arrA[i][j] = VarPolynomial.ZERO;
                }
            }
        }
        for (int i = 0; i < arrAPrime.length; i++) {
            for (int j = 0; j < arrAPrime[i].length; j++) {
                if (arrAPrime[i][j] == null) {
                    arrAPrime[i][j] = VarPolynomial.ZERO;
                }
            }
        }

        // Finally: create the result:
        this.resultLCS = new LCS(
                Matrix.create(arrA), Matrix.create(arrAPrime),
                Matrix.create(b), this.rule);
    }
}
