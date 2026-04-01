package aprove.verification.dpframework.DPProblem.Solvers;

import static aprove.verification.dpframework.BasicStructures.Utility.PoloStrictMode.*;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.QApplicativeUsableRules.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * QDP Polo processor. Tries to orient P and all usable rules of P non-strictly
 * and at least one rule of P strictly, then deletes the strictly oriented
 * rules from P.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class QDPPoloSolver implements ImprovedQActiveSolver {

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Solvers.QDPPoloSolver");

    private POLOFactory factory;

    // build autostrict constraint? (only matters when applicable, of course)
    private boolean autostrict;

    private boolean autostrictJar;

    public QDPPoloSolver(POLOFactory factory, boolean autostrict, boolean autostrictJar) {
        // will be overridden later by the strategy
        this.factory = factory;
        this.autostrict = autostrict;
        this.autostrictJar = autostrictJar;
        // Autostrict as described in the JAR06 paper? (If not, new vars are used)
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R, boolean active, boolean allstrict, Abortion aborter) throws AbortionException {
        POLO solvingOrder;
        POLOSolver solver;
        PoloStrictMode mode = allstrict ? ALLSTRICT : (this.autostrict ? AUTOSTRICT : SEARCHSTRICT);
        QDPPoloSolver.log.log(Level.FINE, "Using mode: {0}\n", mode);

        Set<Constraint<TRSTerm>> pConstraints = Constraint.fromRules(P, mode == ALLSTRICT ? OrderRelation.GR : OrderRelation.GE);
        Triple<POLOSolver, Set<SimplePolyConstraint>, Set<VarPolyConstraint>> solverTriple =
            this.factory.getSolver(pConstraints, R, null, null, aborter);

        solver = solverTriple.x;
        solver.setAllowWeakMonotonicity(true);
        Set<SimplePolyConstraint> noSearchConstraints1 = solverTriple.y;
        Set<VarPolyConstraint> noSearchConstraints2 = solverTriple.z;
        Set<VarPolyConstraint> PConstraints = solver.createPoloConstraints(aborter, pConstraints);
        Set<VarPolyConstraint> searchConstraints;

        // maximizing the value of this polynomial means orienting as many
        // term constraints strictly as possible for the search space
        // (interesting if the SearchAlgorithm in use is able to perform
        // optimization)
        SimplePolynomial maximizeMe = null;
        switch (mode) {
        case AUTOSTRICT :
            maximizeMe = solver.addASC(PConstraints, this.autostrictJar);
            noSearchConstraints2.addAll(PConstraints);
            searchConstraints = null;
            break;
        case ALLSTRICT :
            noSearchConstraints2.addAll(PConstraints);
            searchConstraints = null;
            break;
        case SEARCHSTRICT :
            searchConstraints = PConstraints;
            break;
        default:
            return null;
        }
        try {
            solvingOrder = solver.solve(noSearchConstraints1, noSearchConstraints2, searchConstraints, maximizeMe, aborter);
        } catch (BuiltTooManyException e) {
            return null;
        }

        if (solvingOrder == null) {
//            qdp.dumpCodish(SatSearch.encodeTime, SatSearch.solveTime, SatSearch.decodeTime, 1, 0, "failed", null, null);
            return null;
        }

        if (Globals.useAssertions) {
            Interpretation inter = solvingOrder.getInterpretation();
            for (QActiveCondition qac : R.values()) {
                SimplePolynomial condition = inter.getActiveConstraint(qac);
                if ((! condition.equals(SimplePolynomial.ONE)) &&
                        (! condition.equals(SimplePolynomial.ZERO))) {
                    if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                        String message = "Internal error: having active condition not being 0 or 1 after the polo solution: "+condition;
                        System.err.println(message);
                        System.err.println(P.toString());
                        System.err.println(R.toString());
                        System.err.println(inter);
                        QDPPoloSolver.log.log(Level.SEVERE, message);
                    }
                    if (! Globals.DEBUG_NONE) {
                        assert false : "Internal error: having active condition not being 0 or 1 after the polo solution: "+condition;
                    }
                }
            }
        }

        return solvingOrder;
    }

    @Override
    public boolean improvedSolvingSupported() {
        return this.factory.isSATEngine();
    }

    /**
     * Solves the constraints arising from a reduction pair processor.
     * Here, the sidecondition encodes something like active, and the variables
     * in R denote which rules should be usable.
     */
    @Override
    public Pair<? extends ExportableOrder<TRSTerm>, Set<Variable<AfsProp>>> solve(
            Set<Pair<TRSTerm, TRSTerm>> P,
            Collection<Pair<? extends GeneralizedRule, Variable<AfsProp>>> R,
            Formula<AfsProp> sidecondition,
            boolean allstrict,
            Abortion aborter)
            throws AbortionException {
        DiophantineSATConverter dioSatConv = this.factory.getSATConverterParam();
        if (Globals.useAssertions) {
            assert dioSatConv != null;
        }
        SatEngine satEngine = (SatEngine) this.factory.getSATCheckerFactory();
        BigInteger coeffRange = this.factory.getRangeParam();

        // first convert pairs and rules to (conditional) term constraints.
        Set<Constraint<TRSTerm>> pConstraints = new LinkedHashSet<Constraint<TRSTerm>>(P.size());
        OrderRelation rel = allstrict ? OrderRelation.GR : OrderRelation.GE; // initial constraint type depends on all-strict
        for (Pair<TRSTerm,TRSTerm> s_to_t : P) {
            pConstraints.add(Constraint.create(s_to_t.x, s_to_t.y, rel));
        }

        rel = OrderRelation.GE;
        Collection<Pair<Constraint<TRSTerm>,Variable<AfsProp>>> rConstraints = new ArrayList<Pair<Constraint<TRSTerm>,Variable<AfsProp>>>(R.size());
        for (Pair<? extends GeneralizedRule, Variable<AfsProp>> ruleUsable : R) {
            rConstraints.add(new Pair<Constraint<TRSTerm>, Variable<AfsProp>>(Constraint.fromRule(ruleUsable.x, rel), ruleUsable.y));
        }

        FormulaFactory<Diophantine> dFactory = new FullSharingFactory<Diophantine>();

        // then encode these constraints into a diophantine formula and get
        // the generic interpretation and the mapping of the usable rules variables
        Triple<Formula<Diophantine>,Interpretation,Map<Variable<AfsProp>,Variable<Diophantine>>> dioResult;
        dioResult = this.factory.getEncoding(pConstraints, rConstraints, sidecondition, allstrict, dFactory, aborter);

        aborter.checkAbortion();

        Formula<Diophantine> dioFormula = dioResult.x;
        Interpretation interpretation = dioResult.y;
        Map<Variable<AfsProp>,Variable<Diophantine>> varMap = dioResult.z;

        // now we have to solve the diophantine formula
        Map<String, BigInteger> coeffRanges = new LinkedHashMap<String, BigInteger>(); // no special ranges
        FormulaFactory<None> formulaFactory = satEngine.getFormulaFactory();
        PoloSatConverter converter = dioSatConv.getPoloSatConverter(formulaFactory,
                coeffRanges, coeffRange);


        SatSearch satSearcher = SatSearch.create(satEngine, converter);
        Set<Variable<Diophantine>> trueVars = new HashSet<Variable<Diophantine>>(varMap.values());
        Map<String, BigInteger> solution = satSearcher.search(dioFormula, aborter, trueVars);

        if (solution != null) {
            // we have a solution, so we only need to look for the interesting variables
            // (those which occur in R)
            Set<Variable<AfsProp>> interestingTrueVars = new HashSet<Variable<AfsProp>>();
            for (Pair<?,Variable<AfsProp>> rule : R) {
                Variable<Diophantine> dioVar = varMap.get(rule.y);
                if (Globals.useAssertions) {
                    assert dioVar != null;
                }
                if (trueVars.contains(dioVar)) {
                    interestingTrueVars.add(rule.y);
                }
            }
            interpretation = interpretation.specialize(solution, BigInteger.ZERO);
            return new Pair<POLO,Set<Variable<AfsProp>>>(POLO.create(interpretation), interestingTrueVars);
        } else {
            return null;
        }


    }


}
