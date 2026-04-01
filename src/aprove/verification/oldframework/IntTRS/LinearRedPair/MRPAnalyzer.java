package aprove.verification.oldframework.IntTRS.LinearRedPair;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.LinearRedPair.LinearRedPairProcessor.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.CoefficientConstraint.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This is the LCS-Analyzer, which uses a modification of Rybalchenko's &
 * Podelski's method. MRP stands for Modified Rybalchenko Podelski. Here I
 * assume that all the LCS have to same format to keep things simple.
 * @author Matthias Hoelzel
 */
public class MRPAnalyzer extends AbstractLCSAnalyzer {
    /** Number of LCSs. */
    private final int numberOfLCSs;

    /**
     * Stores the lambdas, which are used to formulate the constraints. For each
     * LCS we use 2 lambdas.
     */
    private final ArrayList<Matrix> lambda1;

    /** See lambda1 */
    private final ArrayList<Matrix> lambda2;

    /**
     * These are coefficients of the resulting interpretation. For each function
     * symbol one may use different coefficients.
     */
    private final LinkedHashMap<FunctionSymbol, Matrix> mu;

    /** Stores list of constraints encoding weak decrease for each LCS */
    private final ArrayList<List<CoefficientConstraint>> weakConstraints;

    /** Stores list of constraints encoding strict decrease for each LCS */
    private final ArrayList<List<CoefficientConstraint>> strictConstraints;

    /** Stores list of constraints encoding compatibility */
    private final LinkedList<CoefficientConstraint> compatibilityConstraints;

    /** Set of function symbols. */
    private final LinkedHashSet<FunctionSymbol> symbols;

    /** The result LCS-system. */
    private List<LCS> resultSystem;

    /** List of dropped LCSs */
    private final List<LCS> droppedLCSs;

    /** Some aborter */
    private final Abortion aborter;

    /**
     * Constructive constructor.
     * @param lcss list of LCSs to be solved
     * @param lrProof the proof we are going to create
     * @param gen NameGenerator
     * @param abortion some aborter, disrupting everything
     */
    public MRPAnalyzer(final List<LCS> lcss, final LinearRankingProof lrProof, final FreshNameGenerator gen,
            final Abortion abortion) {
        super(lcss, lrProof, gen);

        this.aborter = abortion;
        this.numberOfLCSs = this.lcsSystem.size();
        this.lambda1 = new ArrayList<>(this.numberOfLCSs);
        this.lambda2 = new ArrayList<>(this.numberOfLCSs);
        this.symbols =
            new LinkedHashSet<>(this.numberOfLCSs + this.numberOfLCSs);
        this.mu = new LinkedHashMap<>(this.numberOfLCSs + this.numberOfLCSs);

        for (final LCS lcs : this.lcsSystem) {
            assert (lcs.getA().getNumRows() == lcs.getAPrime().getNumRows() && lcs.getA().getNumCols() == lcs.getAPrime().getNumCols()) : "Invalid format!";
        }

        this.weakConstraints = new ArrayList<>(this.numberOfLCSs);
        this.strictConstraints = new ArrayList<>(this.numberOfLCSs);
        this.compatibilityConstraints = new LinkedList<>();
        this.droppedLCSs = new LinkedList<>();
    }

    @Override
    public List<LCS> solve() throws AbortionException {
        if (this.lcsSystem.isEmpty()) {
            this.resultSystem = this.lcsSystem;
        }

        if (this.resultSystem != null) {
            return this.resultSystem;
        }

        // Lets go!
        this.initialize();
        this.buildConstraints();

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("linear");
            l.logln("Here are the constraints: ");

            for (int i = 0; i < this.numberOfLCSs; i++) {
                final LCS lcs = this.lcsSystem.get(i);
                l.logln("" + lcs);
                l.logln("Weak constraints:");
                for (final CoefficientConstraint cc : this.weakConstraints.get(i)) {
                    l.logln(cc);
                }
                l.logln("Strict constraints:");
                for (final CoefficientConstraint cc : this.strictConstraints.get(i)) {
                    l.logln(cc);
                }
            }
            l.logln("Compatibility constraints: ");
            for (final CoefficientConstraint cc : this.compatibilityConstraints) {
                l.logln(cc);
            }
        }

        this.aborter.checkAbortion();
        this.askSMTSolver();

        return this.resultSystem;
    }

    /**
     * Initialized the fields symbols, lambda[1-3], mu.
     */
    private void initialize() {
        // The data-structures have already been created by the constructor,
        // so we only have to fill in some relevant data.

        // 0. Find symbols:
        for (final LCS lcs : this.lcsSystem) {
            this.symbols.add(lcs.getLeftSymbol());
            this.symbols.add(lcs.getRightSymbol());
        }

        // 1. Create lambdas:
        // These are used to build the interpretation & the lower bound in case
        // the SMT-Solver decides to orient a rule strictly.
        for (int i = 0; i < this.numberOfLCSs; i++) {
            final LCS lcs = this.lcsSystem.get(i);
            this.lambda1.add(this.createLambda(lcs));
            this.lambda2.add(this.createLambda(lcs));
        }

        // 2. Create MUs:
        // These are the coefficients we want to find.
        for (final FunctionSymbol sym : this.symbols) {
            this.mu.put(sym, this.createMu(sym));
        }
    }

    /**
     * Creates a lambda.
     * @param lcs the current LCS
     * @return a row-vector in form of a matrix
     */
    private Matrix createLambda(final LCS lcs) {
        final int numOfRows = lcs.getA().getNumRows();

        final VarPolynomial[][] matrix = new VarPolynomial[1][numOfRows];
        for (int i = 0; i < numOfRows; i++) {
            matrix[0][i] = VarPolynomial.createCoefficient(this.ng.getFreshName("l", false));
        }
        return Matrix.create(matrix);
    }

    /**
     * Create a mu. We create a mu, which is a row-vector of variables, for
     * every function symbol. There interpretation will give rise to the
     * interpretation we are looking for.
     * @param sym a function symbol
     * @return a row-vector in form of a matrix
     */
    private Matrix createMu(final FunctionSymbol sym) {
        final VarPolynomial[][] matrix = new VarPolynomial[1][sym.getArity()];
        for (int i = 0; i < sym.getArity(); i++) {
            matrix[0][i] = VarPolynomial.createCoefficient(this.ng.getFreshName("m", false));
        }
        return Matrix.create(matrix);
    }

    /**
     * Constructs the constraint we have to solve.
     */
    private void buildConstraints() {
        this.buildCompatibilityConstraints();
        for (int i = 0; i < this.numberOfLCSs; i++) {
            this.weakConstraints.add(this.buildWeakConstraints(i));
            this.strictConstraints.add(this.buildStrictConstraints(i));
        }
    }

    /** Builds the compatibility constraints */
    private void buildCompatibilityConstraints() {
        for (int i = 0; i < this.numberOfLCSs; i++) {
            final LCS lcs = this.lcsSystem.get(i);
            final Matrix vectorLambda1 = this.lambda1.get(i);
            final Matrix vectorLambda2 = this.lambda2.get(i);
            final Matrix leftMu = this.mu.get(lcs.getLeftSymbol());
            final Matrix rightMu = this.mu.get(lcs.getRightSymbol());

            // (K_1) leftMu + lambda_1 * A = 0
            this.matrixToConstraints(
                leftMu.add(vectorLambda1.multiplyRight(lcs.getA())),
                CoefficientConstraintType.EQ_ZERO,
                this.compatibilityConstraints);

            // (K_2) rightMu - lambda_2 * A' = 0
            this.matrixToConstraints(
                rightMu.minus(vectorLambda2.multiplyRight(lcs.getAPrime())),
                CoefficientConstraintType.EQ_ZERO,
                this.compatibilityConstraints);
        }
    }

    /**
     * Builds the strict constraints
     * @param lcsIndex the current index
     * @return the requested constraints
     */
    private LinkedList<CoefficientConstraint> buildStrictConstraints(final int lcsIndex) {
        final LCS lcs = this.lcsSystem.get(lcsIndex);
        final LinkedList<CoefficientConstraint> constraints =
            new LinkedList<>();
        final Matrix vectorLambda1 = this.lambda1.get(lcsIndex);
        final Matrix vectorLambda2 = this.lambda2.get(lcsIndex);

        // (1) lambda_1 >= 0
        this.matrixToConstraints(vectorLambda1,
            CoefficientConstraintType.GE_ZERO, constraints);

        // (2) lambda_1 * A' = 0
        this.matrixToConstraints(vectorLambda1.multiplyRight(lcs.getAPrime()),
            CoefficientConstraintType.EQ_ZERO, constraints);

        // (3), (4), (5') are the weak constraints. Therefore there is no
        // need to formulate them here again, because they have to hold anyways.

        // (5) lambda_2 * b < 0
        this.matrixToConstraints(vectorLambda2.multiplyRight(lcs.getb()),
            CoefficientConstraintType.LT_ZERO, constraints);

        return constraints;
    }

    /**
     * Builds the weak constraints
     * @param lcsIndex the current index
     * @return the requested constraints
     */
    private LinkedList<CoefficientConstraint> buildWeakConstraints(final int lcsIndex) {
        final LinkedList<CoefficientConstraint> constraints =
            new LinkedList<>();
        final Matrix vectorLambda1 = this.lambda1.get(lcsIndex);
        final Matrix vectorLambda2 = this.lambda2.get(lcsIndex);
        final LCS lcs = this.lcsSystem.get(lcsIndex);

        // (3) lambda_2 >= 0
        this.matrixToConstraints(vectorLambda2,
            CoefficientConstraintType.GE_ZERO, constraints);

        // (4) (lambda_1 - lambda_2) * A = 0
        this.matrixToConstraints(
            vectorLambda1.minus(vectorLambda2).multiplyRight(lcs.getA()),
            CoefficientConstraintType.EQ_ZERO, constraints);

        // (5') lambda_2 * b <= 0
        this.matrixToConstraints(vectorLambda2.multiplyRight(lcs.getb()),
            CoefficientConstraintType.LE_ZERO, constraints);

        return constraints;
    }

    /**
     * Rewrite a whole matrix entry-by-entry to constraints with given type.
     * @param m matrix
     * @param cct type
     * @param toInsert collection to fill in constraints
     */
    private void matrixToConstraints(final Matrix m,
        final CoefficientConstraintType cct,
        final Collection<CoefficientConstraint> toInsert) {
        for (int i = 0; i < m.getNumRows(); i++) {
            for (int j = 0; j < m.getNumCols(); j++) {
                final VarPolynomial vp = m.get(i, j);
                final ImmutableMap<IndefinitePart, SimplePolynomial> varMonomials =
                    vp.getVarMonomials();
                assert varMonomials.size() <= 1 : vp.toString()
                    + " does not have at most one monomial.";
                if (varMonomials.size() == 1) {
                    final SimplePolynomial sp =
                        varMonomials.get(IndefinitePart.ONE);
                    toInsert.add(new CoefficientConstraint(sp, cct));
                } else {
                    toInsert.add(new CoefficientConstraint(
                        SimplePolynomial.ZERO, cct));
                }
            }
        }
    }

    /**
     * Asks the SMT-Solver.
     * @throws AbortionException can be aborted
     */
    private void askSMTSolver() throws AbortionException {
        final FormulaFactory<SMTLIBTheoryAtom> factory =
            new FullSharingFactory<SMTLIBTheoryAtom>();
        final LinkedList<Formula<SMTLIBTheoryAtom>> formulae =
            new LinkedList<>();

        // 1. Turn constraints into SMT-Formulae:
        for (final CoefficientConstraint cc : this.compatibilityConstraints) {
            formulae.add(factory.buildTheoryAtom(cc.toSMTLIBRatTheoryAtom()));
        }
        final LinkedList<Formula<SMTLIBTheoryAtom>> clauses =
            new LinkedList<>();
        for (int i = 0; i < this.numberOfLCSs; i++) {
            for (final CoefficientConstraint cc : this.weakConstraints.get(i)) {
                formulae.add(factory.buildTheoryAtom(cc.toSMTLIBRatTheoryAtom()));
            }

            final LinkedList<Formula<SMTLIBTheoryAtom>> clause =
                new LinkedList<>();
            for (final CoefficientConstraint cc : this.strictConstraints.get(i)) {
                clause.add(factory.buildTheoryAtom(cc.toSMTLIBRatTheoryAtom()));
            }
            clauses.add(factory.buildAnd(clause));
        }
        formulae.add(factory.buildOr(clauses));

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("linear");
            l.logln("Some formulae:");
            l.logln(formulae);
            l.logln();
        }
        this.aborter.checkAbortion();

        // 2. Ask SMT-Solver:
        Pair<YNM, Map<String, String>> answer;
        try {
            answer =
                ToolBox.SMT_ENGINE.solve(formulae, SMTLogic.QF_LRA,
                    this.aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            answer = new Pair<>(YNM.MAYBE, null);
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("linear");
            l.logln("SMT-Solver said " + answer.x);
            l.logln("Solution is " + answer.y.toString());
            l.logln();
        }

        // 3. Build result:
        this.buildResult(answer);
    }

    /**
     * Builds the result.
     * @param answer the result of the SMT-Solver
     */
    private void buildResult(final Pair<YNM, Map<String, String>> answer) {
        if (answer.x == YNM.YES) {
            this.resultSystem = new LinkedList<>();
            final Map<String, String> model = answer.y;

            // 1. Parse rational numbers:
            final Map<String, PreciseRational> ratModel =
                new LinkedHashMap<>(model.size());
            for (final Entry<String, String> e : model.entrySet()) {
                // Turn String into rational:
                final String str = e.getValue();
                final PreciseRational r = PreciseRational.parseRational(str);
                ratModel.put(e.getKey(), r);
            }

            // 2. Calculate the rules, we can drop:
            for (int i = 0; i < this.numberOfLCSs; i++) {
                boolean canBeDropped = true;
                for (final CoefficientConstraint cc : this.strictConstraints.get(i)) {
                    if (!(cc.isSatisfiedByRationalAssignment(ratModel))) {
                        canBeDropped = false;
                        break;
                    }
                }
                if (!canBeDropped) {
                    this.resultSystem.add(this.lcsSystem.get(i));
                } else {
                    this.droppedLCSs.add(this.lcsSystem.get(i));
                }
            }
            this.exportInterpretation(ratModel);
        } else {
            this.resultSystem = this.lcsSystem;
        }
    }

    /**
     * Builds the concrete interpretation and passes it to the proof.
     * @param ratModel a valid model, i.e. a model that satisfies the
     * constraints, constructed by the method buildConstraints.
     */
    private void exportInterpretation(final Map<String, PreciseRational> ratModel) {
        final Map<FunctionSymbol, ArrayList<PreciseRational>> ranking =
            new LinkedHashMap<>(this.symbols.size());

        for (final FunctionSymbol sym : this.symbols) {
            final Matrix symRow = this.mu.get(sym);

            final ArrayList<PreciseRational> coefficients =
                new ArrayList<>(symRow.getNumRows());
            for (int i = 0; i < symRow.getNumCols(); i++) {
                final VarPolynomial vp = symRow.get(0, i);
                final SimplePolynomial sp = vp.getConstantPart();
                final String coeffName = sp.getIndefinites().iterator().next();

                coefficients.add(ratModel.get(coeffName));
            }

            ranking.put(sym, coefficients);
        }

        this.proof.setInterpretation(ranking);
    }

    @Override
    public List<LCS> getDroppedRules() {
        return this.droppedLCSs;
    }

    @Override
    public boolean hasChanged() {
        return !this.droppedLCSs.isEmpty();
    }

}
