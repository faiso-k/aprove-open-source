package aprove.solver;

import java.math.*;
import java.util.*;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Constructs MATROSolvers
 * Heavily based on POLOFactory
 *
 * @author Patrick Kabasci
 */
public class MATROFactory extends SolverFactory {

    private final ArgumentInterpretor argInterpret;
    private final int denominator;
    private final boolean dioLogic;
    private final boolean newSearchStrict;
    private final boolean posFilter;
    private final BigInteger range;
    private final boolean rational;
    private final DiophantineSATConverter satConverter;
    private final SimplificationMode simplification;
    private final boolean simplifyAll; 
    private final boolean stripExponents;
    private final MatrixFactory type;

    @ParamsViaArgumentObject
    public MATROFactory(final Arguments arguments) {
        super(arguments);
        this.argInterpret = arguments.linearity;
        this.denominator = arguments.denominator;
        this.dioLogic = arguments.dioLogic;
        this.newSearchStrict = arguments.newSearchStrict;
        this.posFilter = arguments.posFilter;
        this.range = BigInteger.valueOf(arguments.range);
        this.rational = arguments.rational;
        this.satConverter = arguments.satConverter;
        this.simplification = arguments.simplification;
        this.simplifyAll = arguments.simplifyAll;
        this.stripExponents = arguments.stripExponents;
        this.type = arguments.type;
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
    public MATROSolver getSolver(final Collection<Constraint<TRSTerm>> cons,
        final Collection<Constraint<TRSTerm>> dpcons,
        final boolean active) {
        assert (dpcons != null);
        SearchAlgorithm searchAlg;
        final Engine engine = this.getEngine();

        // so far, we use indefinite-independent ranges for Matro. To change this,
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

        final MatrixFactory fact = this.type.duplicateSelf();
        final ArgumentInterpretor ai = this.argInterpret.duplicateSelf();
        final TermInterpretor ti =
            new TermInterpretor(ImmutableCreator.create(dpsig), ImmutableCreator.create(sig),
                ImmutableCreator.create(vars), fact, ai, this.range, this.rational, this.denominator);
        final MATROSolver solver =
            MATROSolver.create(ti, fact, searchAlg, ai, this.simplification, this.simplifyAll, this.stripExponents,
                this.dioLogic, active, this.newSearchStrict, this.posFilter, this.rational, this.denominator);

        return solver;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        final Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("").info("ENGINE: " + engine);
        return new QDPMatroSolver(this);
    }

    @Override
    public DirectSolver getDirectSolver() {
        return null;
    }
    
    @Override
    public MATROSolver getMLMATROSolver(final ImmutableSet<FunctionSymbol> dpsignature, final ImmutableSet<FunctionSymbol> signature,final ImmutableSet<TRSVariable> variables, final Abortion aborter) throws AbortionException {
        
        /*
        Abortion existingAborter;
        if (aborter != null) {
            existingAborter = aborter;
        } else {
            existingAborter = AbortionFactory.create();
        }
        */
        
        final MatrixFactory fact = this.type.duplicateSelf();
        final ArgumentInterpretor ai = this.argInterpret.duplicateSelf();
        final TermInterpretor ti = new TermInterpretor(dpsignature, signature, variables, fact, ai, this.range, this.dioLogic, this.denominator);
        
        final Engine engine = this.getEngine();
        
        // for this to work one would need to convert BigIntegerInterval to BigInteger
        // final Map<String, BigInteger> specialRanges = ti.getRanges();
        
        final DefaultValueMap<String, BigInteger> allRanges = new DefaultValueMap<String, BigInteger>(this.range);
        // allRanges.putAll(specialRanges);
        
        SearchAlgorithm searchAlg;

        if (engine instanceof SatEngine) {
            // satEngines require a DiophantineSATConverter to build a
            // corresponding SearchAlgorithm, so this workaround is
            // (currently) needed
            final SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(allRanges, this.satConverter);
        } else {
            searchAlg = engine.getSearchAlgorithm(allRanges);
        }
        final MATROSolver solver = MATROSolver.create(ti, fact, searchAlg, ai, this.simplification,
                                                      this.simplifyAll, this.stripExponents, this.simplifyAll, this.dioLogic,
                                                      this.newSearchStrict, this.posFilter, this.rational, this.denominator);
        return solver;
    }

    public Engine checkEngine(Engine engine) {
        if (engine == null) {
            engine = new MINISATEngine(new MINISATEngine.Arguments());
        }
        return engine;
    }

    public static class Arguments extends SolverFactory.Arguments {
        public int denominator;
        public boolean dioLogic;
        public ArgumentInterpretor linearity =
            new aprove.verification.oldframework.Algebra.Matrices.Interpretation.LinearArgumentInterpretor();
        public boolean newSearchStrict;
        public boolean posFilter;
        public int range = Integer.valueOf(MetaSolverFactory.getDefault("MATRO.range"));
        public boolean rational = Boolean.valueOf(MetaSolverFactory.getDefault("MATRO.rational"));
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean simplifyAll;
        public boolean stripExponents;
        public MatrixFactory type;
    }
    
    @Override
    public boolean deliversCPForders() {
        return true;
    }


}
