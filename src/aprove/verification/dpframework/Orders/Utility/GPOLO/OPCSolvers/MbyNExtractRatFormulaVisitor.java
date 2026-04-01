/**
 * @author CKuknat
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author CKuknat
 */
public class MbyNExtractRatFormulaVisitor extends AbstractFormulaPolyExtractor<MbyN> {
    /**
     * This ring is used to operate on the coefficients.
     */
    private Ring<MbyN> ringC;

    /**
     * This monoid is used to operate on monomials over variables.
     */
    private CMonoid<GMonomial<GPolyVar>> monoid;

    /**
     * I need these for having ALL variables after flattening and deleting
     */
    private Set<GPolyVar> variables;

    /**
     * This visitor provides flat representations for a order polynomial.
     */
    private FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar>
        flatteningVisitorOuter;

    /**
     * This visitor provides flat representations for a gpoly (coefficient).
     */

    private FlatteningVisitor<MbyN, GPolyVar> flatteningVisitorInner;

    /**
     * A frequently used pair containing the ring and monoid used to access the
     * monomials.
     */
    private Pair<Semiring<GPoly<MbyN, GPolyVar>>,
        CMonoid<GMonomial<GPolyVar>>> pair;

    /**
     * Remember the (SAT) variable which is the denominator for some (OPC)
     * variable.
     */
    private Map<GPolyVar, GPolyVar> denominators =
        new LinkedHashMap<GPolyVar, GPolyVar>();

    /**
     * Remember the (SAT) variable which is the numerator for some (OPC)
     * variable.
     */
    private Map<GPolyVar, GPolyVar> numerators =
        new LinkedHashMap<GPolyVar, GPolyVar>();

    /**
     * The denominator for all fractions. If null the denominators will be
     * parametric.
     */
    private BigInteger denominator;

    /**
     * Determine whether the inner poly's have to be flattened, too
     */
    private boolean flattenInner;

    /**
     * Create a new ExtractSPCsVisitor.
     * @param ringCParam A ring over C (which is MbyN here).
     * @param polyRingParam A ring over polynomials.
     * @param monoidParam A monoid over monomials over variables.
     * @param fvInner A flattening visitor for coefficient polynomials.
     * @param fvOuter A flattening visitor for order polynomials.
     * @param rangesParam The ranges for the variables.
     * @param varConvParam A variable converter that can store information about
     * the connection between OPC variables and propositional variables.
     * @param defaultRangeParam The range for variables that are not mentioned
     * in rangesParam.
     * @param denominatorParam The fixed value for all denominators. This
     * overrides the ranges setting. Use "null" for denominators according to
     * the ranges.
     */
    public MbyNExtractRatFormulaVisitor(final Ring<MbyN> ringCParam,
            final Ring<GPoly<MbyN, GPolyVar>> polyRingParam,
            final CMonoid<GMonomial<GPolyVar>> monoidParam,
            final FlatteningVisitor<MbyN, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> fvOuter,
            final boolean flattenInner) {
        this.ringC = ringCParam;
        this.monoid = monoidParam;
        this.pair =
            new Pair<Semiring<GPoly<MbyN, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>>(
                    polyRingParam, monoidParam);
        this.variables = new LinkedHashSet<GPolyVar>();
        this.flatteningVisitorInner = fvInner;
        this.flatteningVisitorOuter = fvOuter;
        this.flattenInner = flattenInner;
    }

    public Set<GPolyVar> getVariables() {
        return this.variables;
    }

    /**
     * If an atom is reached, take care of the different variable types and use
     * Absolute Positiveness to generate the resulting formula.
     * @param atom The atom.
     */
    @Override
    public void fcaseAtom(
            final OPCAtom<MbyN> atom) {
        Set<GPolyVar> uqVars = new LinkedHashSet<GPolyVar>();
        Set<GPolyVar> eqVars = null;
        for (OPCQuantifier<MbyN> elem : this.getQuantStack()) {
            if (elem instanceof OPCQuantifierE<?>) {
                eqVars = elem.getQuantifiedVariables();
                this.variables.addAll(elem.getQuantifiedVariables());
            } else if (elem instanceof OPCQuantifierA<?>) {
                uqVars.addAll(elem.getQuantifiedVariables());
            }
        }
        if (Globals.useAssertions) {
            assert(atom.getRightPoly() == null);
            // there may not be a free variable in this atom!
            Set<GPolyVar> allVars =
                new LinkedHashSet<GPolyVar>(atom.getFreeVariables());
            if (eqVars != null) {
                allVars.removeAll(eqVars);
            }
            allVars.removeAll(uqVars);
            assert (allVars.isEmpty());
        }
        Formula<OPCAtom<MbyN>> localConstraints =
            this.getFormulaFactory().buildConstant(true);

        ConstraintType ct = atom.getConstraintType();
        aprove.verification.oldframework.Algebra.Polynomials.ConstraintType coeffCt;
        if (ct.equals(ConstraintType.EQ)) {
            coeffCt = ConstraintType.EQ;
        } else {
            coeffCt = ConstraintType.GE;
        }
        aprove.verification.oldframework.Algebra.Polynomials.ConstraintType constantCt = ct;
        OrderPoly<MbyN> poly = atom.getLeftPoly();
        this.flatteningVisitorOuter.applyTo(poly);

        // there is no need to handle coefficients of variables x,y,.. if there
        // are none.
        if (uqVars.size() > 0) {
            Map<GMonomial<GPolyVar>, GPoly<MbyN, GPolyVar>> map =
                poly.getMonomials(this.pair);
            for (Map.Entry<GMonomial<GPolyVar>, GPoly<MbyN, GPolyVar>> entry
                    : map.entrySet()) {
                GMonomial<GPolyVar> monomial = entry.getKey();
                GPoly<MbyN, GPolyVar> coeffPoly = entry.getValue();
                for (GPolyVar var : uqVars) {
                    if (monomial.getExponents().containsKey(var)) {
                        this.flatteningVisitorInner.applyTo(coeffPoly);
                        Map<GMonomial<GPolyVar>, MbyN> coeffMap =
                            coeffPoly.getMonomials(this.ringC, this.monoid);
                        localConstraints =
                            this.getFormulaFactory().buildAnd(localConstraints,
                                this.createConstraint(coeffMap, coeffCt));
                    }
                }
            }
        }

        // handle the constant part
        GPoly<MbyN, GPolyVar> constant = poly.getConstantPart(this.pair);
        this.flatteningVisitorInner.applyTo(constant);
        Formula<OPCAtom<MbyN>> constConstraint =
            this.createConstraint(constant.getMonomials(
                    this.ringC, this.monoid), constantCt);
        localConstraints = this.getFormulaFactory().buildAnd(
                localConstraints, constConstraint);
        this.buildAnd(this.getFormula(), localConstraints);
    }

    /**
     * Create constraints out of the given map and constraint type.
     *
     * @param map
     *            Each monomial has a coefficient.
     * @param ct
     *            The constraint type.
     * @return The OrderPolyConstraint
     */
    private Formula<OPCAtom<MbyN>> createConstraint(
            final Map<GMonomial<GPolyVar>, MbyN> map, final ConstraintType ct) {
        GPolyFactory<MbyN, GPolyVar> mbynPolyFactory = new FullSharingFactory<MbyN, GPolyVar>();
        GPolyFactory<GPoly<MbyN, GPolyVar>, GPolyVar> mbynPolyFactory2 = new FullSharingFactory<GPoly<MbyN, GPolyVar>, GPolyVar>();
        OrderPolyFactory<MbyN> orderPolyFactory = new OrderPolyFactory<MbyN>(
                mbynPolyFactory2, mbynPolyFactory);

        Set<GPoly<GPoly<MbyN, GPolyVar>, GPolyVar>> newMonomials = new LinkedHashSet<GPoly<GPoly<MbyN, GPolyVar>, GPolyVar>>();
        for (Map.Entry<GMonomial<GPolyVar>, MbyN> entry : map.entrySet()) {
            MbyN mbyn = entry.getValue();
            GPoly<MbyN, GPolyVar> coeff = mbynPolyFactory.buildFromCoeff(mbyn);
            GMonomial<GPolyVar> gMonom = entry.getKey();
            if (this.flattenInner) {
                newMonomials.add(orderPolyFactory.concat(coeff
                        .visit(this.flatteningVisitorInner), VarPartNode
                        .fromMonomial(gMonom)));
            } else {
                newMonomials.add(orderPolyFactory.concat(coeff, VarPartNode
                        .fromMonomial(gMonom)));
            }
        }

        OrderPoly<MbyN> leftPoly = new OrderPoly<MbyN>(orderPolyFactory
                .getFactory().plus(newMonomials));
        OrderPoly<MbyN> rightPoly = new OrderPoly<MbyN>(orderPolyFactory
                .getZero());

        OPCAtom<MbyN> constraint = new OPCAtom<MbyN>(leftPoly, rightPoly, ct);
        return this.getFormulaFactory().buildTheoryAtom(constraint);
    }

    /**
     * @return the numerators.
     */
    public Map<GPolyVar, GPolyVar> getNumerators() {
        if (Globals.useAssertions) {
            assert (this.numerators.keySet().equals(
                    this.denominators.keySet()) || this.denominator != null);
        }
        return this.numerators;
    }

    /**
     * @return the denominators.
     */
    public Map<GPolyVar, GPolyVar> getDenominators() {
        if (Globals.useAssertions) {
            assert (this.numerators.keySet().equals(
                    this.denominators.keySet()) || this.denominator != null);
        }
        return this.denominators;
    }
 }
