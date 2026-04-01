package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.TransitionProgram.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Wraps a FunctionApplication containing the constraint term.
 * @author fab
 *
 */
public class Constraint implements Immutable, HasVariables, HasFunctionSymbols, Exportable {

    private final TRSFunctionApplication t;

    private Constraint(final TRSFunctionApplication t) throws NoConstraintTermException {
        if (!CpxIntTermHelper.isConstraintTerm(t)) {
            throw new NoConstraintTermException(t);
        }
        this.t = t;
    }

    @Override
    public Set<TRSVariable> getVariables() {
        return this.t.getVariables();
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        return this.t.getFunctionSymbols();
    }

    private static SimplePolynomial toSimplePolynomial(final TRSTerm t) throws NotRepresentableAsPolynomialsException {
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable) t;
            return SimplePolynomial.create(v.getName());
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        BigInteger intValue = CpxIntTermHelper.getIntegerValue(fa);
        if (intValue != null) {
            return SimplePolynomial.create(intValue);
        }
        if (CpxIntTermHelper.fAdd.equals(fs)) {
            SimplePolynomial left = Constraint.toSimplePolynomial(fa.getArgument(0));
            SimplePolynomial right = Constraint.toSimplePolynomial(fa.getArgument(1));
            return left.plus(right);
        }
        if (CpxIntTermHelper.fMul.equals(fs)) {
            SimplePolynomial left = Constraint.toSimplePolynomial(fa.getArgument(0));
            SimplePolynomial right = Constraint.toSimplePolynomial(fa.getArgument(1));
            return left.times(right);
        }
        if (CpxIntTermHelper.fSub.equals(fs)) {
            SimplePolynomial left = Constraint.toSimplePolynomial(fa.getArgument(0));
            SimplePolynomial right = Constraint.toSimplePolynomial(fa.getArgument(1));
            return left.minus(right);
        }
        throw new NotRepresentableAsPolynomialsException();
    }

    /**
     * Compute a set of polynomials P such that for every p in P the inequality p >= 0
     * is implied by this constraint (and the SizeMeasure m).
     *
     */
    public Set<SimplePolynomial> computePolynomials() throws NotRepresentableAsPolynomialsException {
        Set<SimplePolynomial> pols = new LinkedHashSet<>();

        FunctionSymbol fs = this.t.getRootSymbol();

        if (fs.getArity() != 2) {
            throw new NotRepresentableAsPolynomialsException();
        }

        TRSTerm l = this.t.getArgument(0);
        TRSTerm r = this.t.getArgument(1);

        // l > r ==> l - r - 1 >= 0
        if (CpxIntTermHelper.fGt.equals(fs)) {
            pols.add(Constraint.toSimplePolynomial(CpxIntTermHelper.subTerms(CpxIntTermHelper.subTerms(l, r), CpxIntTermHelper.ONE)));
            return pols;
        }
        // l >= r ==> l - r > 0
        if (CpxIntTermHelper.fGe.equals(fs)) {
            pols.add(Constraint.toSimplePolynomial(CpxIntTermHelper.subTerms(l, r)));
            return pols;
        }
        // l < r ==> r - l - 1>= 0
        if (CpxIntTermHelper.fLt.equals(fs)) {
            pols.add(Constraint.toSimplePolynomial(CpxIntTermHelper.subTerms(CpxIntTermHelper.subTerms(r, l), CpxIntTermHelper.ONE)));
            return pols;
        }
        // l <= r ==> r - l >= 0
        if (CpxIntTermHelper.fLe.equals(fs)) {
            pols.add(Constraint.toSimplePolynomial(CpxIntTermHelper.subTerms(r, l)));
            return pols;
        }
        // l = r ==> l - r >= 0 && r - l >= 0
        if (CpxIntTermHelper.fEq.equals(fs)) {
            pols.add(Constraint.toSimplePolynomial(CpxIntTermHelper.subTerms(l, r)));
            pols.add(Constraint.toSimplePolynomial(CpxIntTermHelper.subTerms(r, l)));
            return pols;
        }

        throw new NotRepresentableAsPolynomialsException();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util eu) {
        return this.t.export(eu);
    }

    public TRSFunctionApplication getConstraintTerm() {
        return this.t;
    }

    public Constraint applySubstitution(final TRSSubstitution sigma) throws NoConstraintTermException {
        return Constraint.create(this.t.applySubstitution(sigma));
    }

    public Constraint negate() throws NoConstraintTermException {
        FunctionSymbol fs = this.t.getRootSymbol();
        FunctionSymbol nfs;
        if (CpxIntTermHelper.fEq.equals(fs)) {
            nfs = CpxIntTermHelper.fNeq;
        } else if (CpxIntTermHelper.fNeq.equals(fs)) {
            nfs = CpxIntTermHelper.fEq;
        } else if (CpxIntTermHelper.fGt.equals(fs)) {
            nfs = CpxIntTermHelper.fLe;
        } else if (CpxIntTermHelper.fGe.equals(fs)) {
            nfs = CpxIntTermHelper.fLt;
        } else if (CpxIntTermHelper.fLt.equals(fs)) {
            nfs = CpxIntTermHelper.fGe;
        } else if (CpxIntTermHelper.fLe.equals(fs)) {
            nfs = CpxIntTermHelper.fGt;
        } else {
            throw new NoConstraintTermException(this.t);
        }
        return new Constraint(TRSTerm.createFunctionApplication(nfs, this.t.getArguments()));
    }

    public static Constraint create(final TRSFunctionApplication t) throws NoConstraintTermException {
        return new Constraint(t);
    }

    @Override
    public int hashCode() {
        return this.t.hashCode();
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof Constraint) {
            return this.t.equals(((Constraint) other).t);
        }
        return false;
    }

    public Pair<SimplePolynomial, Op> getPolynomialRepresentation() throws NotRepresentableAsPolynomialException {

        TRSFunctionApplication fa = this.getConstraintTerm();
        FunctionSymbol fs = fa.getRootSymbol();
        if (fs.getArity() == 2) {
            SimplePolynomial l = CpxIntTermHelper.toSimplePolynomial(fa.getArgument(0));
            SimplePolynomial r = CpxIntTermHelper.toSimplePolynomial(fa.getArgument(1));

            if (CpxIntTermHelper.fEq.equals(fs)) {
                return new Pair<>(l.minus(r), TransitionProgram.Op.Equal);
            }
            if (CpxIntTermHelper.fGt.equals(fs)) {
                return new Pair<>(l.minus(r).minus(SimplePolynomial.ONE), TransitionProgram.Op.GreaterEqual);
            }
            if (CpxIntTermHelper.fGe.equals(fs)) {
                return new Pair<>(l.minus(r), TransitionProgram.Op.GreaterEqual);
            }
            if (CpxIntTermHelper.fLt.equals(fs)) {
                return new Pair<>(r.minus(l).minus(SimplePolynomial.ONE), TransitionProgram.Op.GreaterEqual);
            }
            if (CpxIntTermHelper.fLe.equals(fs)) {
                return new Pair<>(r.minus(l), TransitionProgram.Op.GreaterEqual);
            }

        }
        throw new NotRepresentableAsPolynomialException();
    }
}
