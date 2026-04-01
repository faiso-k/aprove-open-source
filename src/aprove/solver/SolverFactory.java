package aprove.solver;

import java.util.Collection;
import java.util.Set;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPSizeChangeProcessor.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.orders.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

/**
 * @version $Id$
 */
public abstract class SolverFactory implements java.io.Serializable {

    private final Engine engine;

    /**
     * Constructor for subclasses using {@link ParamsViaArgumentObject} or
     * {@link ParamsViaArguments}
     */
    protected SolverFactory(Arguments arguments) {
        this.engine = arguments.engine;
    }

    protected Engine getEngine() {
        return this.engine;
    }

    /**
     * Constructs a solver based on the DPFramework.
     *
     * @param cons the constraints the solver is supposed to be constructed for.
     * @return the corresponding solver
     */
    public AbortableConstraintSolver<TRSTerm> getSolver(Collection<Constraint<TRSTerm>> cons) {
        throw new UnsupportedOperationException();
    }

    public AbortableConstraintSolver<TRSTerm> getACSolver(Collection<Constraint<TRSTerm>> cons, Set<FunctionSymbol> rSig,
            Set<FunctionSymbol> aSig, Set<FunctionSymbol> acSig,
            Set<FunctionSymbol> cSig) {
        throw new UnsupportedOperationException();
    }

    /**
     * This method is important for POFormula-based solvers (essentially
     * those that search for path orders) that work via an encoding to SAT.
     *
     * @param formulaFactory
     * @return
     */
    public SATEncoder getSATEncoder(FormulaFactory<None> formulaFactory) {
        return null;
    }

    /**
     * This method is probably most useful if you are into SizeChangeNP
     * or if you have some other application where you want to lay your
     * hands on the propositional formula that order search is encoded
     * to.
     *
     * @param formulaFactory - for propositional formulae
     * @return
     */
    public SCNPOrderEncoder getSCNPOrderEncoder(FormulaFactory<None> formulaFactory) {
        throw new UnsupportedOperationException("getSCNPOrderEncoder not implemented for "
                + this.getClass());
    }

    public SATSCTEncoder getSATSCTEncoder(FormulaFactory<None> formulaFactory) {
        throw new UnsupportedOperationException("getSATSCTEncoder not implemented for "
                + this.getClass());
    }

    /**
     * Returns true iff factory is AC compatible e.g. ACRPOS.
     */
    public boolean isACCompatible() {
        return false;
    }

    public DirectSolver getDirectSolver() {
        throw new UnsupportedOperationException();
    }

    public RRRSolver getRRRSolver() {
        throw new UnsupportedOperationException();
    }
   

    public POLOSolver getPOLOSolver(Set<FunctionSymbol> set, Abortion aborter) {
        throw new UnsupportedOperationException();
    }

    public POLOSolver getCPIMLPOLOSolver(Set<FunctionSymbol> defSig, Set<FunctionSymbol> constSig, Abortion aborter) {
        throw new UnsupportedOperationException();
    }

    public POLOSolver getMLPOLOSolver(Set<FunctionSymbol> set, Abortion aborter) {
        throw new UnsupportedOperationException();
    }
    

	public POLOSolver getParkInductionPOLOSolver(Set<FunctionSymbol> signature, Set<FunctionSymbol> defSym, Abortion aborter) {
		throw new UnsupportedOperationException();
	}
    
    public MATROSolver getMLMATROSolver(final ImmutableSet<FunctionSymbol> dpsignature, final ImmutableSet<FunctionSymbol> signature, final ImmutableSet<TRSVariable> variables, final Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }

    public RRRMuSolver getRRRMuSolver() {
        throw new UnsupportedOperationException();
    }

    public QActiveSolver getQActiveSolver() {
        throw new UnsupportedOperationException();
    }

    public IdpIUsableSolver getIdpQUsableSolver() {
        throw new UnsupportedOperationException("not implemented");
    }

    /**
     * Used by QDPTheoremProverProcessor, probably not so useful for
     * other purposes.
     *
     * @return an OrderCalculator for the ordering that corresponds
     *  to this
     */
    public OrderCalculator getOrderCalculator() {
        throw new UnsupportedOperationException("getOrderCalculator() not implemented for "
                + this.getClass());
    }

    public SATCheckerFactory getSATCheckerFactory() {
        return this.getEngine();
    }

    /**
     * Default implementation returns true since many orders are CE-compatible.
     * Override where necessary.
     *
     * @return whether the generated solvers always generate CE-compatible orders
     */
    public boolean solversGenerateCECompatibleOrders() {
        return true;
    }

    public static class Arguments {
        public Engine engine;
    }

    public RuleChecker getRuleChecker() {
        throw new UnsupportedOperationException("getRuleChecker not implemented for " + this.getClass());
    }
    
    /**
     * State whether the generated orders can (at least in some cases) be exported to CPF.
     * Useful in certified mode, to decide whether a search for a specific order should be started at all.
     */
    public abstract boolean deliversCPForders();

            
}
