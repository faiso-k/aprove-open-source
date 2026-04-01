package aprove.solver;

import java.math.*;
import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.LimitPolynomials.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Constructs LimitPOLOSolvers
 * Heavily based on POLOFactory / MATROFactory
 *
 * @author kabasci
 */
public class LimitPOLOFactory extends SolverFactory {

    private final boolean newSearchStrict;
    private final BigInteger range;
    private final DiophantineSATConverter satConverter;
    private final SimplificationMode simplification;
    private final boolean simplifyAll;
    private final boolean stripExponents;

    @ParamsViaArgumentObject
    public LimitPOLOFactory(final Arguments arguments) {
        super(arguments);
        this.newSearchStrict = arguments.newSearchStrict;
        this.range = BigInteger.valueOf(arguments.range);
        this.satConverter = arguments.satConverter;
        this.simplification = arguments.simplification;
        this.simplifyAll = arguments.simplifyAll;
        this.stripExponents = arguments.stripExponents;
    }

    @Override
    public AbortableConstraintSolver<TRSTerm> getSolver(final Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        // FIXME: second argument of getSolver must not be null, provide an empty map?
        assert (false);
        return this.getSolver(cons, null, false);
    }

    /**
     *
     * @param Pconstraints
     * @param usableRules
     * @param params
     * @param aborter, may be null if usableRules are null
     * @throws aprove.strategies.Abortions.AbortionException only if usableRules are non-null
     * @return
     */
    public LimitPOLOSolver getSolver(final Collection<Constraint<TRSTerm>> cons,
        final Collection<Constraint<TRSTerm>> dpcons,
        final boolean active) {
        assert (dpcons != null);
        SearchAlgorithm searchAlg;
        final Engine engine = this.getEngine();

        // so far, we use indefinite-independent ranges for LimitPolo (besides exponents). To change this,
        // adjust allRanges accordingly
        final DefaultValueMap<String, BigInteger> allRanges = new DefaultValueMap<String, BigInteger>(this.range);

        if (engine instanceof SatEngine) {
            // satEngines require a DiophantineSATConverter to build a
            // corresponding SearchAlgorithm, so this workaround is
            // (currently) needed
            final SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(allRanges, this.satConverter);
        } else {
            searchAlg = engine.getSearchAlgorithm(allRanges);
        }

        final Set<FunctionSymbol> sig = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> dpsig = new LinkedHashSet<FunctionSymbol>();
        final Set<aprove.verification.dpframework.BasicStructures.TRSVariable> vars =
            new LinkedHashSet<aprove.verification.dpframework.BasicStructures.TRSVariable>();
        sig.addAll(Constraint.getFunctionSymbols(cons));
        sig.addAll(Constraint.getFunctionSymbols(dpcons));
        vars.addAll(Constraint.getVariables(cons));
        vars.addAll(Constraint.getVariables(dpcons));

        for (final Constraint<TRSTerm> cs : dpcons) {
            // This *should* fail if any of those is a variable: There is no DPair F(x) -> x.
            final FunctionSymbol rsl = ((TRSFunctionApplication) cs.getLeft()).getRootSymbol();
            final FunctionSymbol rsr = ((TRSFunctionApplication) cs.getRight()).getRootSymbol();
            sig.remove(rsl);
            sig.remove(rsr);
            dpsig.add(rsl);
            dpsig.add(rsr);
        }

        final List<FunctionSymbol> RcupPsig = new ArrayList<FunctionSymbol>();
        RcupPsig.addAll(sig);
        RcupPsig.addAll(dpsig);

        final LPOLInterpretor ti = new LPOLInterpretor(ImmutableCreator.create(RcupPsig), 1); // ExpRange so far hard coded.
        final LimitPOLOSolver solver =
            LimitPOLOSolver.create(ti, searchAlg, this.simplification, this.simplifyAll, this.stripExponents, active,
                this.newSearchStrict);

        return solver;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        final Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: " + engine);
        return new QDPLimitPOLOSolver(this);
    }

    @Override
    public DirectSolver getDirectSolver() {
        return null;
    }

    public Engine checkEngine(Engine engine) {
        if (engine == null) {
            engine = new MINISATEngine(new MINISATEngine.Arguments());
        }
        return engine;
    }

    public static class Arguments extends SolverFactory.Arguments {
        public boolean newSearchStrict;
        public int range = Integer.valueOf(MetaSolverFactory.getDefault("LimitPOLO.range"));
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean simplifyAll;
        public boolean stripExponents;
    }
    
    @Override
    public boolean deliversCPForders() {
        return false;
    }


}
