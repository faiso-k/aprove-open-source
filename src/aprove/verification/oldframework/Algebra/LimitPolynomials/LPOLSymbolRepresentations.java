package aprove.verification.oldframework.Algebra.LimitPolynomials;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Stores the required coefficients for a signature in a LPOLO.
 *
 * Can be specialized once a solution has been found,
 * and exported for the proof.
 *
 * @author kabasci
 *
 */
public class LPOLSymbolRepresentations {

    /**
     * Stores the base parts of the coefficients, including the constant coefficient (as argument 0). They have names of the form f/ar(f)_i
     */
    public final Map<FunctionSymbol, Map<Integer, SimplePolynomial>> baseCoefficients = new LinkedHashMap<FunctionSymbol, Map<Integer, SimplePolynomial>> ();
    /**
     * Stores the exponent parts of the coefficients. They have names of the form f/ar(f).X_i
     */
    public final Map<FunctionSymbol, Map<Integer, SimplePolynomial>> exponentCoefficients = new LinkedHashMap<FunctionSymbol, Map<Integer, SimplePolynomial>> ();


    /**
     * Maximum exponent of a single coefficient
     */
    public final int expRange;


    /**
     * Constructs the representations for a given signature
     * @param signature The P cup R signature for the DP Problem, or the R signature for the TRS.
     */
    public LPOLSymbolRepresentations(final List<FunctionSymbol> signature, int expRange) {
        for (final FunctionSymbol fs: signature) {
            // New maps for the new symbol
            this.baseCoefficients.put(fs, new LinkedHashMap<Integer, SimplePolynomial>());
            this.exponentCoefficients.put(fs, new LinkedHashMap<Integer, SimplePolynomial>());

            this.baseCoefficients.get(fs).put(0, SimplePolynomial.create(fs.getName()+"/"+fs.getArity()+"_0"));
            this.exponentCoefficients.get(fs).put(0, SimplePolynomial.create(fs.getName()+"/"+fs.getArity()+".X_0"));

            for (int i=1; i <= fs.getArity(); i++) {
                this.baseCoefficients.get(fs).put(i, SimplePolynomial.create(fs.getName()+"/"+fs.getArity()+"_" + i));
                this.exponentCoefficients.get(fs).put(i, SimplePolynomial.create(fs.getName()+"/"+fs.getArity()+".X_" + i));
            }
        }
        this.expRange = expRange;
    }

    /**
     * Private helper constructor.
     */
    private LPOLSymbolRepresentations(int expRange) {
        this.expRange = expRange;
    }

    /**
     * Specializes SymbolRepresentations, so as to reflect a found order.
     * @param goalState The found order coefficients
     * @return A deep copy of the symbol representations, specialized
     */
    public LPOLSymbolRepresentations specialize(final Map<String, BigInteger> goalState) {
        final LPOLSymbolRepresentations ret = new LPOLSymbolRepresentations(this.expRange);

        for (final Map.Entry<FunctionSymbol, Map<Integer, SimplePolynomial>> fse: this.baseCoefficients.entrySet()) {
            ret.baseCoefficients.put(fse.getKey(), new LinkedHashMap<Integer, SimplePolynomial>());
            for (final Map.Entry<Integer, SimplePolynomial> fsae: fse.getValue().entrySet()) {
                ret.baseCoefficients.get(fse.getKey()).put(fsae.getKey(), fsae.getValue().specialize(goalState));
            }
        }
        for (final Map.Entry<FunctionSymbol, Map<Integer, SimplePolynomial>> fse: this.exponentCoefficients.entrySet()) {
            ret.exponentCoefficients.put(fse.getKey(), new LinkedHashMap<Integer, SimplePolynomial>());
            for (final Map.Entry<Integer, SimplePolynomial> fsae: fse.getValue().entrySet()) {
                ret.exponentCoefficients.get(fse.getKey()).put(fsae.getKey(), fsae.getValue().specialize(goalState));
            }
        }

        return ret;

    }

    /**
     * Exports the representations for a proof. They are exportet in the form "Pol(f/ar(f)(t_1,...,t_n)) = <Polynomial>".
     * @param eu
     * @return
     */
    public String export(final Export_Util eu) {

        final StringBuilder sb = new StringBuilder();
        sb.append(eu.newline());

        // Assumption: Both maps contain the same function symbol. Ensured by the external constructor.
        for (final Map.Entry<FunctionSymbol, Map<Integer, SimplePolynomial>> fse: this.baseCoefficients.entrySet()) {

            final Map<Integer, SimplePolynomial> fseexp = this.exponentCoefficients.get(fse.getKey());
            sb.append(eu.calligraphic("Pol(") +  fse.getKey().getName() + "/" + fse.getKey().getArity());
            if (fse.getKey().getArity() == 0) {
                sb.append("()");
            } else if (fse.getKey().getArity() == 1) {
                sb.append("(t" + eu.sub("1") + ")");
            } else if (fse.getKey().getArity() == 2) {
                sb.append("(t" + eu.sub("1") + ", t" + eu.sub("2")+ ")");
            } else {
                sb.append("(t" + eu.sub("1") + ",...,t" + eu.sub(Integer.toString(fse.getKey().getArity())) + ")");
            }

            sb.append (") = ");
            for (int i=1; i <= fse.getKey().getArity(); i++) {
                sb.append(fse.getValue().get(i).export(eu));
                sb.append(eu.multSign() + eu.calligraphic("X"));
                if (!fseexp.get(i).equals(SimplePolynomial.ZERO)) {
                    sb.append(eu.sup(fseexp.get(i).export(eu)));
                }
                sb.append("t" + eu.sub(Integer.toString(i)));
                sb.append("+");
            }
            sb.append(fse.getValue().get(0).export(eu));

            sb.append(eu.newline());


        }

        return sb.toString();

    }

    /**
     * The additional constraints to ensure the maximum exponent ranges are kept.
     * @return
     */
    public Set<SimplePolyConstraint> getExpRangeConstraints() {
        Set<SimplePolyConstraint> resSet = new LinkedHashSet<SimplePolyConstraint>();

        for (Map<Integer, SimplePolynomial> m: this.exponentCoefficients.values()) {
            for (SimplePolynomial s: m.values()) {
                resSet.add(new SimplePolyConstraint(SimplePolynomial.create(this.expRange).minus(s),ConstraintType.GE));
            }
        }
        return resSet;
    }


    public LimitPolynomial getCoefficientPoly(FunctionSymbol rootSymbol, int i) {

        return LimitPolynomial.create(this.expRange, this.exponentCoefficients.get(rootSymbol).get(i), this.baseCoefficients.get(rootSymbol).get(i));

    }

}
