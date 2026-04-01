package aprove.solver;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.QApplicativeUsableRules.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.OrderCalculators.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.OrderEncoders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.POLO.Interpretation;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.dpframework.TRSProblem.Solvers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.Algebra.Polynomials.SMTSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public class POLOFactory extends SolverFactory {

    private static final long serialVersionUID = 1L;

    private final boolean allowWeakMonotonicity;
    private final boolean autostrict;
    private final boolean autostrictJar;
    private final int degree;
    private final boolean linearMonotone;
    private final int maxSimpleDegree;
    private final BigInteger range;
    private final int restriction;
    private final DiophantineSATConverter satConverter;
    private final SimplificationMode simplification;
    private final boolean simplifyAll;
    private final boolean stripExponents;
    private final SMTLogic smtLogic;

    public static final int SIMPLE_MIXED = Interpretation.SIMPLE_MIXED;
    public static final int SIMPLE = Interpretation.SIMPLE;
    public static final int LINEAR = Interpretation.LINEAR;
    public static final int INDIVIDUAL = Interpretation.INDIVIDUAL;

    @ParamsViaArgumentObject
    public POLOFactory(final Arguments arguments) {
        super(arguments);
        this.allowWeakMonotonicity = arguments.allowWeakMonotonicity;
        this.autostrict = arguments.autostrict;
        this.autostrictJar = arguments.autostrictJar;
        this.degree = arguments.degree;
        this.linearMonotone = arguments.linearMonotone;
        this.maxSimpleDegree = arguments.maxSimpleDegree;
        this.range = BigInteger.valueOf(arguments.range);
        this.restriction = arguments.restriction;
        this.satConverter = arguments.satConverter;
        this.simplification = arguments.simplification;
        this.simplifyAll = arguments.simplifyAll;
        this.stripExponents = arguments.stripExponents;
        this.smtLogic = arguments.smtLogic;
    }

    @Override
    public POLOSolver getSolver(final Collection<aprove.verification.dpframework.Orders.Constraint<TRSTerm>> cons) {
        try {
            return this.getSolver(cons, null, null, null, null).x;
        } catch (final AbortionException e) {
            throw new RuntimeException("Something is wrong in internals of POLOFactory");
            // this should not happen, see docu of called getSolver-method
        }
    }

    /**
     * Encodes the constraints arising from a DP problem for P,R and the sideCondition
     * (active and possible pi-proper) into a diophantine formula and returns additionally
     * the interpretation and
     * the mapping from AfsProp-vars to Dio-vars.
     * @param pConstraints
     * @param rConstraints
     * @param sideCondition
     * @param allstrict
     * @param dFactory
     */
    public Triple<Formula<Diophantine>, Interpretation, Map<Variable<AfsProp>, Variable<Diophantine>>> getEncoding(final Collection<Constraint<TRSTerm>> pConstraints,
        final Collection<Pair<Constraint<TRSTerm>, Variable<AfsProp>>> rConstraints,
        final Formula<AfsProp> sideCondition,
        boolean allstrict,
        final FormulaFactory<Diophantine> dFactory,
        final Abortion aborter) throws AbortionException {

        if (pConstraints.size() == 1) {
            allstrict = true;
        }

        if (this.degree == POLOFactory.INDIVIDUAL) {
            throw new RuntimeException(
                "Degree \"INDIVIDUAL\" is not supported for POLOSolvers in the DPFramework so far!");
        }

        final Iterable<Constraint<TRSTerm>> iter = new Iterable<Constraint<TRSTerm>>() {

            @Override
            public Iterator<Constraint<TRSTerm>> iterator() {
                return new Iterator<Constraint<TRSTerm>>() {

                    Iterator<Constraint<TRSTerm>> Pit = pConstraints.iterator();
                    Iterator<Pair<Constraint<TRSTerm>, Variable<AfsProp>>> Rit = rConstraints.iterator();

                    @Override
                    public boolean hasNext() {
                        if (this.Pit != null) {
                            if (this.Pit.hasNext()) {
                                return true;
                            } else {
                                this.Pit = null;
                            }
                        }
                        return this.Rit.hasNext();
                    }

                    @Override
                    public Constraint<TRSTerm> next() {
                        if (this.Pit != null) {
                            return this.Pit.next();
                        } else {
                            return this.Rit.next().x;
                        }
                    }

                    @Override
                    public void remove() {
                        throw new UnsupportedOperationException();
                    }

                };
            }

        };

        final Interpretation interpretation =
            Interpretation.create(iter, this.degree, this.maxSimpleDegree, this.linearMonotone, aborter);

        // build diophantine formula
        final List<Formula<Diophantine>> finalDioConstraints = new ArrayList<Formula<Diophantine>>(3);
        Formula<Diophantine> dioCons;
        // constraint for P
        dioCons = interpretation.encodePConstraints(pConstraints, allstrict, dFactory, aborter);
        finalDioConstraints.add(dioCons);
        aborter.checkAbortion();

        // constraint for R
        Pair<Formula<Diophantine>, Map<Variable<AfsProp>, Variable<Diophantine>>> usableResult;
        usableResult = interpretation.encodeRuleConstraints(rConstraints, dFactory, aborter);
        dioCons = usableResult.x;
        final Map<Variable<AfsProp>, Variable<Diophantine>> varMap =
            new LinkedHashMap<Variable<AfsProp>, Variable<Diophantine>>(usableResult.y);
        finalDioConstraints.add(dioCons);
        aborter.checkAbortion();

        // constraint for sideCondition
        dioCons = interpretation.encodeActiveConstraint(sideCondition, usableResult.y, dFactory);
        finalDioConstraints.add(dioCons);
        aborter.checkAbortion();

        // build final diophantine formula
        dioCons = dFactory.buildAnd(finalDioConstraints);

        return new Triple<Formula<Diophantine>, Interpretation, Map<Variable<AfsProp>, Variable<Diophantine>>>(dioCons,
            interpretation, varMap);
    }

    /**
     * Convenience method for use if we are not in equational case.
     */
    @Deprecated
    public Triple<POLOSolver, Set<SimplePolyConstraint>, Set<VarPolyConstraint>> getSolver(final Collection<Constraint<TRSTerm>> Pconstraints,
        final Map<Rule, QActiveCondition> usableRules,
        final Abortion aborter) throws AbortionException {
        return this.getSolver(Pconstraints, usableRules, null, null, aborter);
    }

    /**
     * @param Pconstraints
     * @param usableRules
     * @param eSharpConstraints - use null for "not equational"
     * @param usableEqns - use null for "not equational"
     * @param params
     * @param aborter, may be null if usableRules are null
     * @throws AbortionException only if usableRules are non-null
     * @return
     */
    @Deprecated
    public Triple<POLOSolver, Set<SimplePolyConstraint>, Set<VarPolyConstraint>> getSolver(final Collection<Constraint<TRSTerm>> Pconstraints,
        final Map<? extends GeneralizedRule, QActiveCondition> usableRules,
        final Collection<Constraint<TRSTerm>> eSharpConstraints,
        final Map<Equation, QActiveCondition> usableEqns,
        final Abortion aborter) throws AbortionException {

        if (this.degree == POLOFactory.INDIVIDUAL) {
            throw new RuntimeException(
                "Degree \"INDIVIDUAL\" is not supported for POLOSolvers in the DPFramework so far!");
        }

        Collection<Constraint<TRSTerm>> constraintsForSharpSig;
        if (eSharpConstraints == null) {
            constraintsForSharpSig = Pconstraints;
        } else {
            constraintsForSharpSig = new ArrayList<Constraint<TRSTerm>>(Pconstraints.size() + eSharpConstraints.size());
            constraintsForSharpSig.addAll(Pconstraints);
            constraintsForSharpSig.addAll(eSharpConstraints);
        }

        Abortion existingAborter;
        if (aborter != null) {
            existingAborter = aborter;
        } else {
            existingAborter = AbortionFactory.create();
        }

        final Interpretation interpretation =
            Interpretation.create(constraintsForSharpSig, this.degree, this.maxSimpleDegree, this.linearMonotone,
                existingAborter);

        Set<SimplePolyConstraint> activeConstraints;
        Set<VarPolyConstraint> ruleConstraints;
        if (usableRules == null) {
            if (Globals.useAssertions) {
                assert usableEqns == null;
                // otherwise we need to look into
                // Interpretation.getActiveRuleConstraints(...)
            }
            activeConstraints = null;
            ruleConstraints = null;
        } else {
            // in there, the signature of interpretation is extended to
            // interpret the new FunctionSymbols of usableRules/usableEqns
            // as well
            final Pair<Set<SimplePolyConstraint>, Set<VarPolyConstraint>> constraints =
                interpretation.getActiveRuleConstraints(usableRules, usableEqns, this.degree, existingAborter);
            activeConstraints = constraints.x;
            ruleConstraints = constraints.y;
        }

        // Now our Interpretation should also contain the info regarding the ranges
        // for the additional indefinite coefficients aka Diophantine variables.
        final Map<String, BigInteger> specialRanges = interpretation.getSpecialRanges();

        // merge them
        final DefaultValueMap<String, BigInteger> allRanges = new DefaultValueMap<String, BigInteger>(this.range);
        allRanges.putAll(specialRanges);

        SearchAlgorithm searchAlg;
        final Engine engine = this.getEngine(); // which engine should search?
        if (engine instanceof SatEngine) {
            // satEngines require a DiophantineSATConverter to build a
            // corresponding SearchAlgorithm, so this workaround is
            // (currently) needed
            final SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(allRanges, this.satConverter);
        } else if (engine instanceof SMTLIBEngine) {
            if (this.smtLogic == SMTLogic.QF_NIA) {
                searchAlg = new SMTNIASearch(allRanges);
            } else {
                searchAlg = engine.getSearchAlgorithm(allRanges);
            }
        } else {
            searchAlg = engine.getSearchAlgorithm(allRanges);
        }

        final POLOSolver solver =
            POLOSolver.create(interpretation, searchAlg, this.simplification, this.simplifyAll, this.stripExponents);
        solver.setAllowWeakMonotonicity(this.allowWeakMonotonicity);

        return new Triple<POLOSolver, Set<SimplePolyConstraint>, Set<VarPolyConstraint>>(solver, activeConstraints,
            ruleConstraints);
    }
    
    /**
     * @param signature
     * @param aborter
     * @return
     */
    @Override
    public POLOSolver getPOLOSolver(final Set<FunctionSymbol> signature, final Abortion aborter) throws AbortionException {

        if (this.degree == POLOFactory.INDIVIDUAL) {
            throw new RuntimeException(
                "Degree \"INDIVIDUAL\" is not supported for multilinear POLOSolvers in the DPFramework so far!");
        }

        Abortion existingAborter;
        if (aborter != null) {
            existingAborter = aborter;
        } else {
            existingAborter = AbortionFactory.create();
        }

        final Interpretation interpretation =
            Interpretation.createForSignature(signature, this.degree, this.maxSimpleDegree, this.linearMonotone,
                false, existingAborter);

        Set<SimplePolyConstraint> activeConstraints;
        Set<VarPolyConstraint> ruleConstraints;

        // Now our Interpretation should also contain the info regarding the ranges
        // for the additional indefinite coefficients aka Diophantine variables.
        final Map<String, BigInteger> specialRanges = interpretation.getSpecialRanges();

        // merge them
        final DefaultValueMap<String, BigInteger> allRanges = new DefaultValueMap<String, BigInteger>(this.range);
        allRanges.putAll(specialRanges);

        SearchAlgorithm searchAlg;
        final Engine engine = this.getEngine(); // which engine should search?
        if (engine instanceof SatEngine) {
            // satEngines require a DiophantineSATConverter to build a
            // corresponding SearchAlgorithm, so this workaround is
            // (currently) needed
            final SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(allRanges, this.satConverter);
        } else if (engine instanceof SMTLIBEngine) {
            if (this.smtLogic == SMTLogic.QF_NIA) {
                searchAlg = new SMTNIASearch(allRanges);
            } else {
                searchAlg = engine.getSearchAlgorithm(allRanges);
            }
        } else {
            searchAlg = engine.getSearchAlgorithm(allRanges);
        }

        final POLOSolver solver =
            POLOSolver.create(interpretation, searchAlg, this.simplification, this.simplifyAll, this.stripExponents);
        solver.setAllowWeakMonotonicity(this.allowWeakMonotonicity);

        return solver;
    }
    
    /**
     * @param signature
     * @param aborter
     * @return
     */
    public POLOSolver getMLPOLOSolver(final Set<FunctionSymbol> signature, final Abortion aborter) throws AbortionException {

        if (this.degree == POLOFactory.INDIVIDUAL) {
            throw new RuntimeException(
                "Degree \"INDIVIDUAL\" is not supported for multilinear POLOSolvers in the DPFramework so far!");
        }

        Abortion existingAborter;
        if (aborter != null) {
            existingAborter = aborter;
        } else {
            existingAborter = AbortionFactory.create();
        }

        final Interpretation interpretation =
            Interpretation.createForSignature(signature, this.degree, this.maxSimpleDegree, this.linearMonotone,
                true, existingAborter);

        Set<SimplePolyConstraint> activeConstraints;
        Set<VarPolyConstraint> ruleConstraints;

        // Now our Interpretation should also contain the info regarding the ranges
        // for the additional indefinite coefficients aka Diophantine variables.
        final Map<String, BigInteger> specialRanges = interpretation.getSpecialRanges();

        // merge them
        final DefaultValueMap<String, BigInteger> allRanges = new DefaultValueMap<String, BigInteger>(this.range);
        allRanges.putAll(specialRanges);

        SearchAlgorithm searchAlg;
        final Engine engine = this.getEngine(); // which engine should search?
        if (engine instanceof SatEngine) {
            // satEngines require a DiophantineSATConverter to build a
            // corresponding SearchAlgorithm, so this workaround is
            // (currently) needed
            final SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(allRanges, this.satConverter);
        } else if (engine instanceof SMTLIBEngine) {
            if (this.smtLogic == SMTLogic.QF_NIA) {
                searchAlg = new SMTNIASearch(allRanges);
            } else {
                searchAlg = engine.getSearchAlgorithm(allRanges);
            }
        } else {
            searchAlg = engine.getSearchAlgorithm(allRanges);
        }

        final POLOSolver solver =
            POLOSolver.create(interpretation, searchAlg, this.simplification, this.simplifyAll, this.stripExponents);
        solver.setAllowWeakMonotonicity(this.allowWeakMonotonicity);

        return solver;
    }
    
    /**
     * @param signature
     * @param aborter
     * @return
     */
    @Override
    public POLOSolver getCPIMLPOLOSolver(final Set<FunctionSymbol> defSig, final Set<FunctionSymbol> constSig, final Abortion aborter) throws AbortionException {

        if (this.degree == POLOFactory.INDIVIDUAL) {
            throw new RuntimeException(
                "Degree \"INDIVIDUAL\" is not supported for multilinear POLOSolvers in the DPFramework so far!");
        }

        Abortion existingAborter;
        if (aborter != null) {
            existingAborter = aborter;
        } else {
            existingAborter = AbortionFactory.create();
        }

        final Interpretation interpretation =
            Interpretation.createForSignature(defSig, this.degree, this.maxSimpleDegree, this.linearMonotone,
                true, existingAborter);
        
        for(FunctionSymbol f : constSig) {
            if(this.degree == 0) {
                interpretation.extend(f, 0, aborter);
            } else {
                interpretation.extend(f, 1, aborter);
            }
        }

        Set<SimplePolyConstraint> activeConstraints;
        Set<VarPolyConstraint> ruleConstraints;

        // Now our Interpretation should also contain the info regarding the ranges
        // for the additional indefinite coefficients aka Diophantine variables.
        final Map<String, BigInteger> specialRanges = interpretation.getSpecialRanges();

        // merge them
        final DefaultValueMap<String, BigInteger> allRanges = new DefaultValueMap<String, BigInteger>(this.range);
        allRanges.putAll(specialRanges);

        SearchAlgorithm searchAlg;
        final Engine engine = this.getEngine(); // which engine should search?
        if (engine instanceof SatEngine) {
            // satEngines require a DiophantineSATConverter to build a
            // corresponding SearchAlgorithm, so this workaround is
            // (currently) needed
            final SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(allRanges, this.satConverter);
        } else if (engine instanceof SMTLIBEngine) {
            if (this.smtLogic == SMTLogic.QF_NIA) {
                searchAlg = new SMTNIASearch(allRanges);
            } else {
                searchAlg = engine.getSearchAlgorithm(allRanges);
            }
        } else {
            searchAlg = engine.getSearchAlgorithm(allRanges);
        }

        final POLOSolver solver =
            POLOSolver.create(interpretation, searchAlg, this.simplification, this.simplifyAll, this.stripExponents);
        solver.setAllowWeakMonotonicity(this.allowWeakMonotonicity);

        return solver;
    }

    @Override
    public QActiveSolver getQActiveSolver() {
        final Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("aprove.solver.POLOFactory").info(
            "ENGINE: " + engine + "\n");
        if (engine instanceof YNMPEVLEngine) {
            return new QDPAfsOrderSolver(this, this.restriction);
        } else {
            return new QDPPoloSolver(this, this.autostrict, this.autostrictJar);
        }
    }

    @Override
    public DirectSolver getDirectSolver() {
        final Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("aprove.solver.POLOFactory").info(
            "ENGINE: " + engine + "\n");
        return new AbortableDirectSolver(this);
    }

    @Override
    public RRRSolver getRRRSolver() {
        final Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("aprove.solver.POLOFactory").info(
            "ENGINE: " + engine + "\n");
        return new RRRPoloSolver(this, this.autostrict, this.autostrictJar);
    }

    @Override
    public RRRMuSolver getRRRMuSolver() {
        final Engine engine = this.checkEngine(this.getEngine());
        java.util.logging.Logger.getLogger("aprove.solver.POLOFactory").info(
            "ENGINE: " + engine + "\n");
        return new RRRMuPoloSolver(this, this.autostrict, this.autostrictJar);
    }

    @Override
    public SCNPOrderEncoder getSCNPOrderEncoder(final FormulaFactory<None> formulaFactory) {
        return new SCNPPoloEncoder(formulaFactory, this.satConverter, this.range, this.degree, this.maxSimpleDegree,
            this.linearMonotone);
    }

    @Override
    public OrderCalculator getOrderCalculator() {
        final POLOCalculator result = POLOCalculator.create(this);
        return result;
    }

    public boolean isSATEngine() {
        final Engine engine = this.checkEngine(this.getEngine());
        return engine instanceof SatEngine;
    }

    private Engine checkEngine(Engine engine) {
        if (engine == null) {
            engine = new SAT4JEngine(new SAT4JEngine.Arguments());
        }
        return engine;
    }

    // For QDPPoloSolver
    public DiophantineSATConverter getSATConverterParam() {
        return this.satConverter;
    }

    public BigInteger getRangeParam() {
        return this.range;
    }

    public static class Arguments extends SolverFactory.Arguments {
        public boolean allowWeakMonotonicity = false;
        public boolean autostrict = Boolean.valueOf(MetaSolverFactory.getDefault("POLO.autostrict"));
        public boolean autostrictJar = Boolean.valueOf(MetaSolverFactory.getDefault("POLO.autostrict_jar"));
        public int degree = Integer.valueOf(MetaSolverFactory.getDefault("POLO.degree"));
        public boolean linearMonotone;
        public int maxSimpleDegree = Integer.valueOf(MetaSolverFactory.getDefault("POLO.maxSimpleDegree"));
        public int range = Integer.valueOf(MetaSolverFactory.getDefault("POLO.range"));
        public int restriction = Integer.valueOf(MetaSolverFactory.getDefault("POLO.restriction"));
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean simplifyAll;
        public boolean stripExponents;
        public SMTLogic smtLogic = SMTLogic.QF_LIA;
    }
    
    @Override
    public boolean deliversCPForders() {
        return true;
    }

}
