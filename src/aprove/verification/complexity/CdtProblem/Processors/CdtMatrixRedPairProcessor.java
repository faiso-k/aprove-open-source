package aprove.verification.complexity.CdtProblem.Processors;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

/**
 * RedPairP from Lars Noschinski's diploma thesis, but only for matrix
 * orders.
 *
 * TODO: Generalize.
 */
public class CdtMatrixRedPairProcessor extends CdtProblemProcessor {

    private final int dimension;
    private final int range;
    private final SatEngine engine;
    private final SimplificationMode simplificationMode;

    @ParamsViaArgumentObject
    public CdtMatrixRedPairProcessor(Arguments arguments) {
        this.dimension = arguments.dimension;
        this.range = arguments.range;
        this.engine = arguments.engine;
        this.simplificationMode = arguments.simplificationMode;
    }

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {

        MATROSolver complexitySolver = this.getMatroSolver(cdtProblem);

        // FIXME: Implement active conditions for CdtProblems, then replace this hack
        // with QTRSProblem.
        QTRSProblem qtrs = QTRSProblem.create(cdtProblem.getR()).createInnermost();
        QUsableRules quc = new QUsableRules(qtrs);

        Set<Rule> tupleRules = new LinkedHashSet<Rule>();
        Set<Rule> strictTupleRules = new LinkedHashSet<Rule>();
        Set<Rule> nonStrictTupleRules = new LinkedHashSet<Rule>();
        for (Cdt cdt : cdtProblem.getTuples()) {
            Rule tupleRule = cdt.getRule();
            tupleRules.add(tupleRule);
            if (cdtProblem.getS().contains(cdt)) {
                strictTupleRules.add(tupleRule);
            } else {
                nonStrictTupleRules.add(tupleRule);
            }
        }

        Map<Constraint<TRSTerm>, QActiveCondition> cs =
            new LinkedHashMap<Constraint<TRSTerm>, QActiveCondition>();
        Map<Rule, QActiveCondition> activeConditions = quc.getActiveConditions(tupleRules);
        for (Map.Entry<Rule,QActiveCondition> e : activeConditions.entrySet()) {
            cs.put(Constraint.fromRule(e.getKey(), OrderRelation.GE), e.getValue());
        }
        for (Map.Entry<Rule,QActiveCondition> e : QUsableRules.getRulesAsConditionMap(nonStrictTupleRules).entrySet()) {
            cs.put(Constraint.fromRule(e.getKey(), OrderRelation.GE), e.getValue());
        }
        /* The constraint is GE here, as the MATROSolver will create searchstrict-constrainst*/
        Collection<Constraint<TRSTerm>> dpcs = Constraint.fromRules(strictTupleRules, OrderRelation.GE);
        QActiveOrder order = complexitySolver.solveComplexity(cs, dpcs, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful("Could not find a suitable reduction pair");
        }

        Set<Rule> usableRules = new HashSet<>();

        for (final Map.Entry<Rule, QActiveCondition> entry : quc.getActiveConditions(tupleRules, false).entrySet()) {
            if (order.checkQActiveCondition(entry.getValue())) {
                usableRules.add(entry.getKey());
            }
        }


        /* find strict tuples */
        Set<Cdt> tuplesFoundStrict = new LinkedHashSet<Cdt>();
        for (Cdt cdt : cdtProblem.getTuples()) {
            if (!cdtProblem.getS().contains(cdt)
                    && cdtProblem.getK().contains(cdt)) {
                continue;
            }

            Constraint<TRSTerm> c = Constraint.fromRule(cdt.getRule(), OrderRelation.GR);
            if (order.solves(c)) {
                tuplesFoundStrict.add(cdt);
            }
        }

        if (Globals.useAssertions && order != null) {
            assert(!tuplesFoundStrict.isEmpty());
        }

        LinkedHashSet<Cdt> newS = new LinkedHashSet<Cdt>(cdtProblem.getS());
        newS.removeAll(tuplesFoundStrict);
        LinkedHashSet<Cdt> newK = new LinkedHashSet<Cdt>(cdtProblem.getK());
        newK.addAll(tuplesFoundStrict);
        CdtProblem newCdtProblem = cdtProblem.createSubproblem(
                cdtProblem.getGraph(),
                ImmutableCreator.create(newS),
                ImmutableCreator.create(newK));

        // TODO: Extract degree from interpretation; can give a better bound.
        return ResultFactory.proved(
                newCdtProblem,
                UpperBound.create(new SumComputation(ComplexityValue.fixedDegreePoly(Math.abs(dimension)))),
                new CdtPolyRedPairProcessor.CdtRuleRemovalProof(order,cdtProblem.getTuples(),tuplesFoundStrict,usableRules));
    }

    @SuppressWarnings("unchecked")
    private MATROSolver getMatroSolver(CdtProblem cdtProblem) {
        Set<TRSVariable> vars =
            (Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(cdtProblem.getR());
        vars.addAll(
            (Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(cdtProblem.getTuples())
        );
        ImmutableSet<FunctionSymbol> compoundSymbols = cdtProblem.getCompoundSymbols();
        Set<FunctionSymbol> tupleSymbols = cdtProblem.getTupleSymbols();
        tupleSymbols.addAll(compoundSymbols);
        Set<FunctionSymbol> nonTupleSymbols = new LinkedHashSet<FunctionSymbol>(cdtProblem.getSignature());
        nonTupleSymbols.removeAll(tupleSymbols);
        FormulaFactory<None> formulaFactory = this.engine.getFormulaFactory();
        PoloSatConverter converter =
            PlainSPCToCircuitConverter.create(
                formulaFactory,
                Collections.<String,BigInteger>emptyMap(),
                BigInteger.valueOf(this.range),
                new PoloSatConfigInfo()
            );
        SatSearch satSearch = SatSearch.create(this.engine, converter);
        MATROSolver complexitySolver =
            MATROSolver.createPolComplexity(
                satSearch,
                this.simplificationMode,
                true,
                true,
                true,
                ImmutableCreator.create(tupleSymbols),
                ImmutableCreator.create(nonTupleSymbols),
                compoundSymbols,
                cdtProblem.getDefinedRSymbols(),
                ImmutableCreator.create(vars),
                this.dimension,
                BigInteger.valueOf(this.range)
            );
        return complexitySolver;
    }

    public static class Arguments {
        public int range;
        public int dimension;
        public SatEngine engine;
        public SimplificationMode simplificationMode = SimplificationMode.MAXIMUM;
    }

}
