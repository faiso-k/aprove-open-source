/*
 * Created on 15.03.2005
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.xml.*;
import immutables.*;

/**
 * Linear polynomial order with negative constants. Uses approximations
 * p_left and p_right (cf. Hirokawa & Middeldorp, Information and Computation 2007
 * or Fuhs & Giesl & Middeldorp & Schneider-Kamp & Thiemann & Zankl, Proc. SAT'07).
 *
 * @author fuhs
 */
public class NegPolyOrder implements QActiveOrder, QActiveCondition.Afs {

    final static String orderName = "Polynomial ordering with negative constants";

    /**
     * currently we only handle linear polynomial interpretations
     * for NegPolo:
     * the int[] encodes as first element the constant part,
     * next the coefficients for the arguments.
     * E.g. if interpretation(cons) = [-2,0,3] then
     * Pol(cons(s,t)) = -2 + 0*Pol(s) + 3*Pol(t)
     */

    private Map<FunctionSymbol, int[]> interpretation;

    public NegPolyOrder(final Map<FunctionSymbol, int[]> interpretation) {
        this.interpretation = interpretation;
    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) {
        if (Options.certifier.isCeta()) {
            return this.solveWithPLeftRight(c);
        }

        PEP pet = PEP.create(c, true);
        for (final Map.Entry<FunctionSymbol, int[]> entry : this.interpretation.entrySet()) {
            pet = pet.specialize(entry.getKey(), entry.getValue());
        }
        if (pet.isCompletelySpecified()) {
            return pet.checkNonNegative();
        }
        this.interpretation = new LinkedHashMap<FunctionSymbol, int[]>(this.interpretation);
        for (final FunctionSymbol unknown : pet.getMissingInterpretations()) {
            final int n = unknown.getArity();
            final int[] inter = new int[n+1];
            for (int i=0; i<=n; i++) {
                inter[i] = 1;
            }
            this.interpretation.put(unknown, inter);
        }
        // the above code specializes the interpretation if
        // necessary
        return this.solves(c);
    }

    private boolean solveWithPLeftRight(final Constraint<TRSTerm> c) {
        VarPolynomial tLeft = null, tRight = null, pDiff;
        tLeft = this.leftApprox(c.x);
        tRight = this.rightApprox(c.y);
        pDiff = tLeft.minus(tRight);
        final OrderRelation rel = c.getType();
        ConstraintType type;
        switch (rel) {
        case GE:
            type = ConstraintType.GE;
            break;
        case GR:
            type = ConstraintType.GT;
            break;
        default:
            throw new RuntimeException("NEFPOLO cannot handle constraint type "
                    + rel + " !");
        }
        VarPolyConstraint pDiffConstraint;
        pDiffConstraint = new VarPolyConstraint(pDiff, type);
        return pDiffConstraint.isValid();
    }

    /**
     * This method computes the underApproximation of definition 8 of
     * http://verify.rwth-aachen.de/fuhs/papers/SAT07-satpolo.pdf
     *
     * @param l
     * @return the approximation
     */
    private VarPolynomial leftApprox(final TRSTerm l) {
        VarPolynomial result;
        if (l.isVariable()) {
            result = VarPolynomial.createVariable(((TRSVariable) l).getName());
        } else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            final TRSFunctionApplication fApp = (TRSFunctionApplication) l;
            final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            final int[] fInter = this.interpretation.get(fApp.getRootSymbol());

            assert (fInter.length > 0);

            final ArrayList<VarPolynomial> monomials = new ArrayList<VarPolynomial>(
                    fInter.length);
            monomials.add(VarPolynomial.create(fInter[0]));
            for (int i = 1; i < fInter.length; i++) {
                final VarPolynomial constPart = VarPolynomial.create(fInter[i]);
                monomials.add(constPart.times(this.leftApprox(args.get(i - 1))));
            }
            // calculate p1
            final VarPolynomial p1 = VarPolynomial.plus(monomials);

            final SimplePolynomial simpleConstant = p1.getConstantPart();
            final VarPolynomial constPart = VarPolynomial.create(simpleConstant);
            final VarPolynomial nonConstPart = p1.minus(constPart);

            // if l = f(t_1, ... , t_n), ncon(p1) = 0, and 0 > con(p1) return p1
            if (nonConstPart.equals(VarPolynomial.ZERO)
                    && simpleConstant.getNumericalAddend().compareTo(
                            BigInteger.ZERO) < 0) {
                result = VarPolynomial.ZERO;
            } else {
                result = p1;
            }
        }
        return result;
    }

    /**
     * This method computes the overApproximation of definition 8 of
     * http://verify.rwth-aachen.de/fuhs/papers/SAT07-satpolo.pdf
     *
     * @param r
     * @return the approximation
     */
    private VarPolynomial rightApprox(final TRSTerm r) {
        VarPolynomial result;
        if (r.isVariable()) {
            result = VarPolynomial.createVariable(((TRSVariable) r).getName());
        } else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            final TRSFunctionApplication fApp = (TRSFunctionApplication) r;
            final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            final int[] fInter = this.interpretation.get(fApp.getRootSymbol());

            assert (fInter.length > 0);

            final ArrayList<VarPolynomial> monomials = new ArrayList<VarPolynomial>(
                    fInter.length);
            monomials.add(VarPolynomial.create(fInter[0]));
            for (int i = 1; i < fInter.length; i++) {
                final VarPolynomial constPart = VarPolynomial.create(fInter[i]);
                monomials.add(constPart.times(this.rightApprox(args.get(i - 1))));
            }
            // calculate p2
            final VarPolynomial p2 = VarPolynomial.plus(monomials);

            final SimplePolynomial simpleConstant = p2.getConstantPart();
            final VarPolynomial constPart = VarPolynomial.create(simpleConstant);
            final VarPolynomial nonConstPart = p2.minus(constPart);

            // if r = f(t_1, ... , t_n) and 0 > con(p2) return ncon(p2)
            if (simpleConstant.getNumericalAddend().compareTo(BigInteger.ZERO) < 0) {
                result = nonConstPart;
            } else {
                result = p2;
            }

        }
        return result;
    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) {
        return this.solves(Constraint.create(s, t, OrderRelation.GR));
    }

    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
        return this.solves(Constraint.create(s, t, OrderRelation.EQ));
    }


    public static String export(final Export_Util o, final int[] inter) {
        boolean first = true;
        final StringBuilder s = new StringBuilder();
        int i = 1;
        final int n = inter.length;
        while (i < n) {
            final int c = inter[i];
            if (c > 0) {
                if (first) {
                    first = false;
                } else {
                    s.append(o.export(" + "));
                }
                if (c > 1) {
                    s.append(o.export(c));
                }
                s.append(o.export("x"));
                s.append(o.sub(""+i));
            }
            i++;
        }
        final int c = inter[0];
        if (first) {
            s.append(o.export(c));
        } else {
            if (c > 0) {
                s.append(o.export(" + "+c));
            } else if (c < 0) {
                s.append(o.export(" - " + (-c)));
            }
        }
        String res = s.toString();
        if (c < 0) {
            res = o.export("max{0, ")+s+o.export("}");
        }
        return res;
    }

    private final static Citation[] citations = new Citation[]{Citation.NEGPOLO, Citation.POLO};

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Polynomial Order "+o.cite(NegPolyOrder.citations)+" with Interpretation:\n"));
        s.append(o.linebreak());
        for (final Map.Entry<FunctionSymbol, int[]> entry : this.interpretation.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final int arity = f.getArity();
            String fString = o.export(f);
            if (arity >= 1) {
                fString += o.export("(x") + o.sub(""+1);
                if (arity > 2) {
                    fString += o.export(", ...");
                }
                if (arity >= 2) {
                    fString += o.export(", x")+o.sub(""+arity);
                }
                fString += ")";
            }
            String fToPol = o.bold("POL( ")+fString+o.bold(" )")+o.export(" = ");

            // TODO (cf. Interpretation.java)
            fToPol += NegPolyOrder.export(o, entry.getValue());
            s.append(o.indent(o.math(fToPol)));
            s.append(o.linebreak());
        }
        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public boolean checkQActiveCondition(QActiveCondition qac) {
        qac = qac.specialize(this);
        if (qac.isBoolean()) {
            return qac == QActiveCondition.TRUE;
        } else {
            throw new RuntimeException("qactive condition should be evaluatable at this point");
        }
    }

    @Override
    public YNM filterPosition(final FunctionSymbol f, final int i) {
        final int[] inter = this.interpretation.get(f);
        if (inter == null) {
            return YNM.MAYBE;
        }
        return YNM.fromBool(inter[i+1] != 0);
    }

    private static Element intToCPF(Document doc, int i) {
        return CPFTag.POLYNOMIAL.create(doc,
                CPFTag.COEFFICIENT.create(doc,
                        CPFTag.INTEGER.create(doc,i)));
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element interpretation = CPFTag.INTERPRETATION.create(doc,
                CPFTag.TYPE.create(doc,
                        CPFTag.POLYNOMIAL.create(doc,
                                CPFTag.DOMAIN.create(doc, CPFTag.NATURALS.create(doc)),
                                CPFTag.DEGREE.create(doc, doc.createTextNode("1")))));
        for (final Map.Entry<FunctionSymbol, int[]> inter : this.interpretation.entrySet()) {
            final int[] coeffs = inter.getValue();
            List<Element> coefficients = new ArrayList<>(coeffs.length);
            final FunctionSymbol f = inter.getKey();
            for (int i = 0; i < coeffs.length; i++) {
                final int coeff = coeffs[i];
                if (coeff == 0) {
                    continue;
                }
                if (i == 0) {
                    coefficients.add(NegPolyOrder.intToCPF(doc, coeff));
                } else {
                    Element var = CPFTag.POLYNOMIAL.create(doc,
                            CPFTag.VARIABLE.create(doc,
                                    doc.createTextNode("" + i)));
                    if (coeff == 1) {
                        coefficients.add(var);
                    } else {
                        coefficients.add(CPFTag.POLYNOMIAL.create(doc,
                                CPFTag.PRODUCT.create(doc, NegPolyOrder.intToCPF(doc, coeff), var)));
                    }
                }
            }
            int n = coefficients.size();
            Element poly;
            if (n > 1) {
                final Element sum = CPFTag.SUM.create(doc);
                for (Element monomial : coefficients) {
                    sum.appendChild(monomial);
                }
                poly = CPFTag.POLYNOMIAL.create(doc, sum);
            } else {
                poly = n == 0 ? NegPolyOrder.intToCPF(doc, 0) : coefficients.get(0);
            }
            interpretation.appendChild(CPFTag.INTERPRET.create(doc,
                    f.toCPF(doc, xmlMetaData),
                    CPFTag.ARITY.create(doc, doc.createTextNode(f.getArity() + "")),
                    poly));
        }
        return CPFTag.ORDERING_CONSTRAINT_PROOF.create(doc,
                CPFTag.RED_PAIR.create(doc,
                        interpretation));
    }

    @Override
    public String isCPFSupported() {
        return null;
    }

}
