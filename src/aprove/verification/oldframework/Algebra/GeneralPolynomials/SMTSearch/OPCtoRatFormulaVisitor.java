package aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch;

import java.util.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

/**
 * Generates a propositional formula from the OrderPolyConstraint it visits.
 *
 * @author CKuknat
 */
public class OPCtoRatFormulaVisitor<C extends GPolyCoeff, Dest> extends
        ConstraintVisitor.ConstraintVisitorSkeleton<C> {

    /**
     * The converter used to convert sth. like a linear poly frome a non linear
     * one
     */
    private TheoryConverter<OrderPolyConstraint<C>, Dest> theoryConverter;

/**
     * Used to build order polys
     */
    private OrderPolyFactory<C> orderPolyFactory;

    /**
     * Used to build propositional formulae.
     */
    private FormulaFactory<Dest> formulaFactory;

    /**
     * A cache for sub-formulae. Used to retrieve information about sub-nodes,
     * and prevent multiple generation of identical formulae.
     */
    private Map<OrderPolyConstraint<C>, Formula<Dest>> formulaCache;

    /**
     * A cache for logical variables. Used to map OPCLogVars to variables.
     */
    private final Map<OPCLogVar<C>, Variable<Dest>> variableCache;

    /**
     * During the generation process, this always holds the formula corresponding
     * to the last visited node. Thus, when the process is finished, it holds the
     * one corresponding to the topmost node, i.e. the whole constraint.
     */
    private Formula<Dest> formula;

    public OPCtoRatFormulaVisitor(
            final TheoryConverter<OrderPolyConstraint<C>, Dest> theoryConverter,
            final OrderPolyFactory<C> orderPolyFactory,
            final FormulaFactory<Dest> formulaFactory) {
        this.theoryConverter = theoryConverter;
        this.orderPolyFactory = orderPolyFactory;
        this.formulaFactory = formulaFactory;
        this.formulaCache = new HashMap<OrderPolyConstraint<C>, Formula<Dest>>();
        this.variableCache = new LinkedHashMap<OPCLogVar<C>, Variable<Dest>>();
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
        Formula<Dest> cachedValue = this.formulaCache.get(subCon);
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
        Formula<Dest> cachedValue = this.formulaCache.get(subCon);
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
        Formula<Dest> cachedValue = this.formulaCache.get(param);
        if (cachedValue == null) {
            Set<OrderPolyConstraint<C>> operands = param.getOperands();
            List<Formula<Dest>> formulae = new LinkedList<Formula<Dest>>();
            for (OrderPolyConstraint<C> subCon : operands) {
                formulae.add(this.formulaCache.get(subCon));
            }
            Formula<Dest> formula = this.formulaFactory.buildAnd(formulae);
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
        Formula<Dest> cachedValue = this.formulaCache.get(param);
        if (cachedValue == null) {
            Set<OrderPolyConstraint<C>> operands = param.getOperands();
            List<Formula<Dest>> formulae = new LinkedList<Formula<Dest>>();
            for (OrderPolyConstraint<C> subCon : operands) {
                formulae.add(this.formulaCache.get(subCon));
            }
            Formula<Dest> formula = this.formulaFactory.buildOr(formulae);
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
        Formula<Dest> cachedValue = this.formulaCache.get(param);
        if (cachedValue == null) {
            /*
             * Attention, this only works because the right side is 0 (in what
             * way ever)
             *
             * OrderPoly<C> newLeft =
             * orderPolyFactory.minus(param.getLeftPoly(),
             * param.getRightPoly()); OPCAtom<C> atom = new OPCAtom<C>(newLeft,
             * orderPolyFactory .getZero(), param.getConstraintType());
             */

            Formula<Dest> formula;
            // formula = this.theoryConverter.convert(atom);

            formula = this.theoryConverter.convert(param);

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
        Formula<Dest> trueFormula = this.formulaFactory.buildConstant(true);
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
        Formula<Dest> falseFormula = this.formulaFactory.buildConstant(false);
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
        Formula<Dest> cachedValue = this.formulaCache.get(param);
        if (cachedValue == null) {
            Formula<Dest> formula = this.formulaCache.get(param.getSub());
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
    public Formula<Dest> getFormula() {
        return this.formula;
    }

    /**
     * @return the formula corresponding to the constraint last visited;
     *  will include the accumulated side constraints as top level
     *  conjuncts if bounded arithmetic is used;
     *  purges some SAT-related internal data structures in the process
     */
    public Formula<Dest> getFormulaWithCleanup() {
        Formula<Dest> res = this.getFormula();
        this.orderPolyFactory = null;
        this.theoryConverter = null;
        this.formula = null;
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
        Variable<Dest> cachedValue = this.variableCache.get(param);
        if (cachedValue == null) {
            Variable<Dest> formula = this.formulaFactory.buildVariable();
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
        for (Map.Entry<OPCLogVar<C>, Variable<Dest>> e : this.variableCache
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
