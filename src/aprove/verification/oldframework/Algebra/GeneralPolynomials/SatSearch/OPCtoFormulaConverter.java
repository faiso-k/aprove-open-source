package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch;

import java.util.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Generates a propositional formula from the OrderPolyConstraint it visits.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class OPCtoFormulaConverter<C extends GPolyCoeff> extends
        ConstraintVisitor.ConstraintVisitorSkeleton<C> {

    /**
     * The visitor used to generate circuits from polynomials.
     */
    private final PolyToCircuitConverter<C, GPolyVar> polyToCircuit;

    /**
     * Used to build circuits.
     */
    private CircuitFactory circuitFactory;

    /**
     * Are we using bounded arithmetic?
     */
    private final boolean usesBoundedArithmetic;

    /**
     * Used to build propositional formulae.
     */
    private FormulaFactory<None> formulaFactory;

    /**
     * A cache for sub-formulae. Used to retrieve information about sub-nodes,
     * and prevent multiple generation of identical formulae.
     */
    private Map<OrderPolyConstraint<C>, Formula<None>> formulaCache;

    /**
     * A cache for logical variables. Used to map OPCLogVars to variables.
     */
    private final Map<OPCLogVar<C>, Variable<None>> variableCache;

    /**
     * If we are using bounded arithmetic, we additionally require
     * these side constraints to hold. The idea is that they ensure
     * that no overflows occur for any used value.
     */
    private List<Formula<None>> sideConstraints;

    /**
     * During the generation process, this always holds the formula corresponding
     * to the last visited node. Thus, when the process is finished, it holds the
     * one corresponding to the topmost node, i.e. the whole constraint.
     */
    private Formula<None> formula;

    public OPCtoFormulaConverter(
            final PolyToCircuitConverter<C, GPolyVar> polyToCircuit,
            final FormulaFactory<None> formulaFactory) {
        this.polyToCircuit = polyToCircuit;
        this.circuitFactory = polyToCircuit.getFactory();
        this.usesBoundedArithmetic = this.circuitFactory.usesBoundedArithmetic();
        if (this.usesBoundedArithmetic) {
            this.sideConstraints = new ArrayList<Formula<None>>(2048);
        }
        this.formulaFactory = formulaFactory;
        this.formulaCache = new HashMap<OrderPolyConstraint<C>, Formula<None>>();
        this.variableCache = new LinkedHashMap<OPCLogVar<C>, Variable<None>>();
    }

    /**
     * Start visiting the given constraint and clean up afterwards.
     * @param constraint The constraint that should be visited.
     * @return Some new constraint.
     */
    @Override
    public OrderPolyConstraint<C> applyToWithCleanup(final OrderPolyConstraint<C> constraint) {
        final OrderPolyConstraint<C> result = this.applyTo(constraint);
        this.formulaCache = null;
        // this.formulaFactory = null;
        // we exclude this.sideConstraints and this.formulaFactory
        // from the cleanup since they contains data that will still
        // be needed later when invoking this.getFormula()
        return result;
    }

    /**
     * Quantifiers are not relevant for the generation process, so this
     * just copies the formula corresponding to the child constraint.
     * @param param the visited constraint.
     * @param newConstraint not used.
     * @return not used.
     */
    @Override
    public OrderPolyConstraint<C> caseQuantifierE(
            final OPCQuantifierE<C> param,
            final OrderPolyConstraint<C> newConstraint) {
        OrderPolyConstraint<C> subCon = param.getInnerConstraint();
        Formula<None> cachedValue = this.formulaCache.get(subCon);
        this.formulaCache.put(param, cachedValue);
        this.formula = cachedValue;
        return param;
    }

    /**
     * Quantifiers are not relevant for the generation process, so this
     * just copies the formula corresponding to the child constraint.
     *
     * @param param the visited constraint.
     * @param newConstraint not used.
     * @return not used.
     */
    @Override
    public OrderPolyConstraint<C> caseQuantifierA(
            final OPCQuantifierA<C> param,
            final OrderPolyConstraint<C> newConstraint) {
        OrderPolyConstraint<C> subCon = param.getInnerConstraint();
        Formula<None> cachedValue = this.formulaCache.get(subCon);
        this.formulaCache.put(param, cachedValue);
        this.formula = cachedValue;
        return param;
    }

    /**
     * Builds the conjunction of the formulae corresponding to
     * the visited constraint's children.
     * @param param the visited constraint.
     * @param newOperands not used.
     * @return not used.
     */
    @Override
    public OrderPolyConstraint<C> caseAnd(
            final OPCAnd<C> param,
            final Set<OrderPolyConstraint<C>> newOperands) {
        Formula<None> cachedValue = this.formulaCache.get(param);
        if (cachedValue == null) {
            Set<OrderPolyConstraint<C>> operands = param.getOperands();
            List<Formula<None>> formulae = new LinkedList<Formula<None>>();
            for (OrderPolyConstraint<C> subCon : operands) {
                formulae.add(this.formulaCache.get(subCon));
            }
            Formula<None> formula = this.formulaFactory.buildAnd(formulae);
            this.formulaCache.put(param, formula);
            this.formula = formula;
        } else {
            this.formula = cachedValue;
        }
        return param;
    }

    /**
     * Builds the disjunction of the formulae corresponding to
     * the visited constraint's children.
     * @param param the visited constraint.
     * @param newOperands not used.
     * @return not used.
     */
    @Override
    public OrderPolyConstraint<C> caseOr(
            final OPCOr<C> param,
            final Set<OrderPolyConstraint<C>> newOperands) {
        Formula<None> cachedValue = this.formulaCache.get(param);
        if (cachedValue == null) {
            Set<OrderPolyConstraint<C>> operands = param.getOperands();
            List<Formula<None>> formulae = new LinkedList<Formula<None>>();
            for (OrderPolyConstraint<C> subCon : operands) {
                formulae.add(this.formulaCache.get(subCon));
            }
            Formula<None> formula = this.formulaFactory.buildOr(formulae);
            assert(formula != null);
            this.formulaCache.put(param, formula);
            this.formula = formula;
        } else {
            this.formula = cachedValue;
        }
        return param;
    }

    /**
     * Builds the formula corresponding to an atomic constraint (l REL r).
     * The real work here is done by a PolyToCircuitConverter and a CircuitFactory.
     * @param param the visited constraint.
     * @return not used.
     */
    @Override
    public OrderPolyConstraint<C> caseAtom(final OPCAtom<C> param) {
        Formula<None> cachedValue = this.formulaCache.get(param);
        if (cachedValue == null) {
            Pair<PolyCircuit, Overflows> left, right;
            if (param.getLeftPoly() == null) {
                left = new Pair<PolyCircuit, Overflows>(
                           this.polyToCircuit.getBinarizer().zero(),
                           Overflows.NO_OVERFLOWS);
            } else {
                param.getLeftPoly().getInnerPoly().visit(this.polyToCircuit);
                left = this.polyToCircuit.getCircuitWithOverflows();
            }
            if (param.getRightPoly() == null) {
                right = new Pair<PolyCircuit, Overflows>(
                            this.polyToCircuit.getBinarizer().zero(),
                            Overflows.NO_OVERFLOWS);
            } else {
                param.getRightPoly().getInnerPoly().visit(this.polyToCircuit);
                right = this.polyToCircuit.getCircuitWithOverflows();
            }
            Formula<None> formula;
            switch (param.getConstraintType()) {
            case EQ:
                formula = this.circuitFactory.buildEQCircuit(left.x.getFormulae(), right.x.getFormulae());
                break;
            case GE:
                formula = this.circuitFactory.buildGECircuit(left.x.getFormulae(), right.x.getFormulae()).x;
                break;
            case GT:
                formula = this.circuitFactory.buildGTCircuit(left.x.getFormulae(), right.x.getFormulae());
                break;
            default:
                throw new IllegalArgumentException("Unknown constraint type!");
            }
            if (this.usesBoundedArithmetic) {
                Overflows localOverflows = Overflows.merge(left.y, right.y);
                Formula<None> boundsNotExceeded =
                    localOverflows.ensureAllOverflowsZero(this.formulaFactory);
                Formula<None> atomImpliesBoundsNotExceeded =
                    this.formulaFactory.buildImplication(formula, boundsNotExceeded);
                this.sideConstraints.add(atomImpliesBoundsNotExceeded);
            }
            this.formulaCache.put(param, formula);
            this.formula = formula;
        } else {
            this.formula = cachedValue;
        }
        return param;
    }

    /**
     * Builds the formula representing the boolean constant `true`.
     * @param param the visited constraint (a True node).
     * @return not used.
     */
    @Override
    public OrderPolyConstraint<C> caseTrue(final OPCTrue<C> param) {
        Formula<None> trueFormula = this.formulaFactory.buildConstant(true);
        this.formulaCache.put(param, trueFormula);
        this.formula = trueFormula;
        return param;
    }

    /**
     * Builds the formula representing the boolean constant `false`.
     * @param param the visited constraint (a False node).
     * @return not used.
     */
    @Override
    public OrderPolyConstraint<C> caseFalse(final OPCFalse<C> param) {
        Formula<None> falseFormula = this.formulaFactory.buildConstant(false);
        this.formulaCache.put(param, falseFormula);
        this.formula = falseFormula;
        return param;
    }

    /**
     * Builds the negation of the formulae corresponding to
     * the visited constraint's child.
     * @param param the visited constraint.
     * @param newConstraint not used.
     * @return not used.
     */
    @Override
    public OrderPolyConstraint<C> caseNot(
            final OPCNot<C> param,
            final OrderPolyConstraint<C> newConstraint) {
        Formula<None> cachedValue = this.formulaCache.get(param);
        if (cachedValue == null) {
            Formula<None> formula = this.formulaCache.get(param.getSub());
            formula = this.formulaFactory.buildNot(formula);
            this.formulaCache.put(param, formula);
            this.formula = formula;
        } else {
            this.formula = cachedValue;
        }
        return param;
    }

    /**
     * @return the formula corresponding to the constraint last visited;
     *  will include the accumulated side constraints as top level
     *  conjuncts if bounded arithmetic is used
     */
    public Formula<None> getFormula() {
        if (this.usesBoundedArithmetic) {
            List<Formula<None>> overallConstraints = new ArrayList<Formula<None>>(
                    this.sideConstraints.size() + 1);
            overallConstraints.addAll(this.sideConstraints);
            overallConstraints.add(this.formula);
            Formula<None> res = this.formulaFactory
                    .buildAnd(overallConstraints);
            return res;
        }
        else {
            return this.formula;
        }
    }

    /**
     * @return the formula corresponding to the constraint last visited;
     *  will include the accumulated side constraints as top level
     *  conjuncts if bounded arithmetic is used;
     *  purges some SAT-related internal data structures in the process
     */
    public Formula<None> getFormulaWithCleanup() {
        Formula<None> res = this.getFormula();
        this.circuitFactory = null;
        this.formula = null;
        this.sideConstraints = null;
        this.formulaFactory = null;
        return res;
    }

    /**
     * Avoid UnsupportedOperationException
     */
    @Override
    public void fcaseLogVar(OPCLogVar<C> param) {
    }

    /**
     * Builds a fresh variable the first time the OPCLogVar is visited
     * and uses it for succeeding calls with equal param.
     */
    @Override
    public OrderPolyConstraint<C> caseLogVar(OPCLogVar<C> param) {
        Variable<None> cachedValue = this.variableCache.get(param);
        if (cachedValue == null) {
            Variable<None> formula = this.formulaFactory.buildVariable();
            this.formulaCache.put(param, formula);
            this.variableCache.put(param, formula);
            this.formula = formula;
        } else {
            this.formula = cachedValue;
        }
        return param;
    }

    public Map<OPCLogVar<C>, Boolean> getLogState(int[] solution) {
        Map<Integer, OPCLogVar<C>> idToVar = new LinkedHashMap<Integer, OPCLogVar<C>>();
        for (Map.Entry<OPCLogVar<C>, Variable<None>> e : this.variableCache
                .entrySet()) {
            idToVar.put(e.getValue().getId(), e.getKey());
        }
        Map<OPCLogVar<C>, Boolean> logState = new LinkedHashMap<OPCLogVar<C>, Boolean>();
        for(OPCLogVar<C> v : this.variableCache.keySet()) {
            logState.put(v, Boolean.FALSE);
        }
        for (int id : solution) {
            logState.put(idToVar.get(id), Boolean.TRUE);
        }
        return logState;
    }
}
