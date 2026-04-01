package aprove.input.Diophantine;

import java.math.*;
import java.util.*;

import aprove.input.Generated.diophantine.analysis.*;
import aprove.input.Generated.diophantine.node.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 *
 * @author bearperson
 * @version $Id$
 */
public class GPolyPass<C extends GPolyCoeff> extends DepthFirstAdapter {

    private BigInteger baseInt = null;
    // Hack for doing base/exponent stuff: Exactly one of those three will be non-null in outAPowerPowerof()
    // and in outAPosfactorFactor(), initially set by outA*Base()
    private GPoly<C, GPolyVar> basePoly = null;
    private VarPartNode<GPolyVar> baseVarPart = null;
    // The coefficient collects all constant factors in the current addend
    private final Stack<BigInteger> coefficientStack = new Stack<BigInteger>();

    private Set<OrderPolyConstraint<C>> constraints;
    // Factories needed to create the poly, pretty immutable
    private final GPolyCoeffFactory<C> creator;
    private ConstraintType ct = null;
    private Set<GPolyVar> eVars;
    private final GPolyFactory<C, GPolyVar> innerFactory;
    // True if we have a constraint like x <= y, meaning that we need to swap sides and do y - x >= 0
    private Boolean isLt = null;

    /* From here on, we have the pieces of polynomials. Due to (), we may be constructing polynomials
     * inside other polynomials. This is why everything from here on is a stack of whatever you'd
     * intuitively use. (with apologies to the pointy-brackets-haters)
     */
    /* This name is not strictly correct, if ()-expressions are used it may contain full polys already
     * Basic use: contains the sum pieces of our polynomial, so adding these gives our poly.
     */
    private final Stack<List<GPoly<C, GPolyVar>>> monomialsStack = new Stack<List<GPoly<C, GPolyVar>>>();
    private final OrderPolyFactory<C> opf;
    private final Stack<GPoly<C, GPolyVar>> polyStack = new Stack<GPoly<C, GPolyVar>>();
    // Data used in building polyconstraints
    private OrderPolyConstraint<C> result;

    private final SimpleFactory<C> sf;
    // This one collects all sub-polynomials in the current addend
    private final Stack<List<GPoly<C, GPolyVar>>> subPolysStack = new Stack<List<GPoly<C, GPolyVar>>>();
    // The varParts are things like x^2 or y^3 in the current addend
    private final Stack<List<VarPartNode<GPolyVar>>> varPartsStack = new Stack<List<VarPartNode<GPolyVar>>>();

    public GPolyPass(final GPolyCoeffFactory<C> creator) {
        this.creator = creator;
        GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> outerFactory;

        this.sf = new SimpleFactory<C>();
        outerFactory = new FullSharingFactory<GPoly<C, GPolyVar>, GPolyVar>();
        this.innerFactory = new FullSharingFactory<C, GPolyVar>();
        this.opf = new OrderPolyFactory<C>(outerFactory, this.innerFactory);

    }

    @Override
    public void caseAEqRelation(final AEqRelation node) {
        this.isLt = Boolean.FALSE;
        this.ct = ConstraintType.EQ;
    }

    @Override
    public void caseAGteRelation(final AGteRelation node) {
        this.isLt = Boolean.FALSE;
        this.ct = ConstraintType.GE;
    }

    @Override
    public void caseAGtRelation(final AGtRelation node) {
        this.isLt = Boolean.FALSE;
        this.ct = ConstraintType.GT;
    }

    @Override
    public void caseALteRelation(final ALteRelation node) {
        this.isLt = Boolean.TRUE;
        this.ct = ConstraintType.GE;
    }

    @Override
    public void caseALtRelation(final ALtRelation node) {
        this.isLt = Boolean.TRUE;
        this.ct = ConstraintType.GT;
    }

    public OrderPolyConstraint<C> getConstraints() {
        return this.result;
    }

    @Override
    public void inAAddend(final AAddend node) {
        this.varPartsStack.push(new ArrayList<VarPartNode<GPolyVar>>());
        this.coefficientStack.push(BigInteger.ONE);
        this.subPolysStack.push(new ArrayList<GPoly<C, GPolyVar>>());
    }

    @Override
    public void inAPolynomial(final APolynomial node) {
        this.monomialsStack.push(new ArrayList<GPoly<C, GPolyVar>>());
    }

    @Override
    public void inStart(final Start node) {
        this.constraints = new LinkedHashSet<OrderPolyConstraint<C>>();
        this.eVars = new LinkedHashSet<GPolyVar>();
        this.result = null;
    }

    @Override
    public void outAAddend(final AAddend node) {
        final List<VarPartNode<GPolyVar>> varParts = this.varPartsStack.pop();
        final BigInteger coefficient = this.coefficientStack.pop();
        final List<GPoly<C, GPolyVar>> subPolys = this.subPolysStack.pop();

        // First, multiply all variable parts together
        VarPartNode<GPolyVar> varPart = this.innerFactory.getVarOne();
        for (final VarPartNode<GPolyVar> part : varParts) {
            varPart = this.innerFactory.times(varPart, part);
        }

        // Now, add the coefficient to make a GPoly
        final C coeff = this.creator.fromInteger(coefficient);
        GPoly<C, GPolyVar> result = this.innerFactory.concat(coeff, varPart);

        // Finally, if neccessary, multiply with subpolynomials
        for (final GPoly<C, GPolyVar> subPoly : subPolys) {
            result = this.innerFactory.times(result, subPoly);
        }
        this.monomialsStack.peek().add(result);
    }

    @Override
    public void outABracketsBase(final ABracketsBase base) {
        // just a bit ago, outAPolynomial will have pushed our poly here
        final GPoly<C, GPolyVar> subPoly = this.polyStack.pop();
        this.basePoly = subPoly;
    }

    @Override
    public void outADiophantine(final ADiophantine node) {
        final GPoly<C, GPolyVar> right = this.polyStack.pop();
        final GPoly<C, GPolyVar> left = this.polyStack.pop();
        GPoly<C, GPolyVar> innerPoly;
        if (this.isLt) {
            innerPoly = this.innerFactory.minus(right, left);
        } else {
            innerPoly = this.innerFactory.minus(left, right);
        }
        final OrderPoly<C> op = this.opf.buildFromCoeff(innerPoly);
        final OrderPolyConstraint<C> constraint = this.sf.createWithQuantifier(op, this.ct);

        /* Technically not neccessary, but this may help debugging if for some weird reason,
         * these don't get [re]set during processing of another diophantine.
         */
        this.isLt = null;
        this.ct = null;

        this.eVars.addAll(innerPoly.getVariables());
        this.constraints.add(constraint);
    }

    @Override
    public void outAIntegerBase(final AIntegerBase node) {
        final String text = node.getInt().getText();
        final long myInt = Long.parseLong(text);
        // valueOf is more efficient as it reuses values. Hopefully, we won't have constants > Long.MAX_VALUE
        this.baseInt = BigInteger.valueOf(myInt);
    }

    @Override
    public void outANegfactorFactor(final ANegfactorFactor node) {
        final BigInteger coefficient = this.coefficientStack.pop();
        this.coefficientStack.push(coefficient.negate());
    }

    @Override
    public void outAPolynomial(final APolynomial node) {
        final List<GPoly<C, GPolyVar>> monomials = this.monomialsStack.pop();
        final GPoly<C, GPolyVar> poly = this.innerFactory.plus(monomials);
        this.polyStack.push(poly);
    }

    @Override
    public void outAPosfactorFactor(final APosfactorFactor node) {
        // Exactly one of the following three must be non-null by the time we get here.
        if (this.basePoly != null) {
            this.subPolysStack.peek().add(this.basePoly);
            this.basePoly = null;
        } else if (this.baseVarPart != null) {
            this.varPartsStack.peek().add(this.baseVarPart);
            this.baseVarPart = null;
        } else if (this.baseInt != null) {
            final BigInteger coefficient = this.coefficientStack.pop();
            this.coefficientStack.push(coefficient.multiply(this.baseInt));
            this.baseInt = null;
        } else {
            // Should never happen - outAPosfactorFactor called, but no outA*Base ever got called
            throw new IllegalStateException("outAPosfactorFactor called, but no outA*Base ever got called");
        }
    }

    @Override
    public void outAPowerPowerof(final APowerPowerof node) {
        final String text = node.getInt().getText();
        final int exponent = Integer.parseInt(text);
        // Exactly one of the following four must be non-null by the time we get here.
        if (this.basePoly != null) {
            this.basePoly = this.innerFactory.power(this.basePoly, BigInteger.valueOf(exponent));
        } else if (this.baseVarPart != null) {
            this.baseVarPart = this.innerFactory.power(this.baseVarPart, BigInteger.valueOf(exponent));
        } else if (this.baseInt != null) {
            this.baseInt = this.baseInt.pow(exponent);
        } else {
            // Should never happen - outAPowerPowerof called, but no outA*Base ever got called
            throw new IllegalStateException("outAPowerPowerof called, but no outA*Base ever got called");
        }
    }

    @Override
    public void outAVariableBase(final AVariableBase node) {
        final String text = node.getVar().getText();
        final GPolyVar var = GAtomicVar.createVariable(text);
        this.baseVarPart = this.innerFactory.buildVariable(var);
    }

    @Override
    public void outStart(final Start node) {
        final OrderPolyConstraint<C> opc = this.sf.createAnd(this.constraints);
        this.result = this.sf.createQuantifierE(opc, this.eVars);
    }
}
