package aprove.verification.dpframework.PADPProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class PlainLinearInterpretation implements Exportable {

    private LinkedHashMap<FunctionSymbol, LinearParamTerm> theMap;
    private Set<String> allCoeff;
    private Set<String> monoCoeff;

    /**
     * Construct a PlainLinearInterpretation.
     */
    public PlainLinearInterpretation(Set<FunctionSymbol> funs) {
        this.theMap = new LinkedHashMap<FunctionSymbol, LinearParamTerm>();
        this.allCoeff = new LinkedHashSet<String>();
        this.monoCoeff = new LinkedHashSet<String>();
        for (FunctionSymbol f : funs) {
            this.theMap.put(f, this.getPoly(f));
        }
    }

    private PlainLinearInterpretation() {
        this.theMap = new LinkedHashMap<FunctionSymbol, LinearParamTerm>();
        this.allCoeff = new LinkedHashSet<String>();
        this.monoCoeff = new LinkedHashSet<String>();
    }

    private LinearParamTerm getPoly(FunctionSymbol f) {
        int arity = f.getArity();
        String name = f.getName();
        LinearParamTerm[] vars = new LinearParamTerm[arity];
        for (int i = 0; i < arity; i++) {
            vars[i] = new LinearParamTerm(TRSTerm.createVariable("X_" + (i + 1)));
        }
        String coeff = name + "_" + (arity + 1);
        this.allCoeff.add(coeff);
        LinearParamTerm res = new LinearParamTerm(coeff);
        for (int i = 0; i < arity; i++) {
            coeff = name + "_" + (i + 1);
            this.allCoeff.add(coeff);
            this.monoCoeff.add(coeff);
            SimplePolynomial c_i = SimplePolynomial.create(coeff);
            res = res.add(vars[i].mult(c_i));
        }
        return res;
    }

    /**
     * Returns all coefficients.
     */
    public Set<String> getCoefficients() {
        return this.allCoeff;
    }

    /**
     * Returns all coefficients that need to be >0 for monotonicity.
     */
    public Set<String> getMonoCoefficients() {
        return this.monoCoeff;
    }

    public LinearParamTerm getInterpretation(TRSTerm t) {
        LinearParamTerm res;
        if (t.isVariable()) {
            res = new LinearParamTerm((TRSVariable) t);
        } else {
            TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            if (args.isEmpty()) {
                return this.theMap.get(fApp.getRootSymbol());
            }
            // compute the interpretations of the arguments
            int size = args.size();
            Map<TRSVariable, LinearParamTerm> subst = new LinkedHashMap<TRSVariable, LinearParamTerm>(size);
            for (int i = 0; i < size; i++) {
                TRSVariable argVar = TRSTerm.createVariable("X_" + (i + 1));
                LinearParamTerm argPoly = this.getInterpretation(args.get(i));
                subst.put(argVar, argPoly);
            }
            // get the interpretation of the root symbol
            LinearParamTerm tmp = this.theMap.get(fApp.getRootSymbol());
            // and plug the arg polys into the root poly
            res = tmp.substituteVariables(subst);
        }
        return res;
    }

    public LinearParamTerm getInterpretation(PARule rule) {
        return this.getInterpretation(rule.getLeft()).minus(this.getInterpretation(rule.getRight()));
    }

    public LinearParamTerm getInterpretation(Rule rule) {
        return this.getInterpretation(rule.getLeft()).minus(this.getInterpretation(rule.getRight()));
    }

    public LinearParamTerm getInterpretation(Equation eqn) {
        return this.getInterpretation(eqn.getLeft()).minus(this.getInterpretation(eqn.getRight()));
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder result = new StringBuilder("Plain-Polynomial interpretation:\n");

        int size = this.theMap.size();
        List<String> rows = new ArrayList<String>(size);

        Map<FunctionSymbol, LinearParamTerm> sortedMap = new TreeMap<FunctionSymbol, LinearParamTerm>(this.theMap);
        for (Map.Entry<FunctionSymbol, LinearParamTerm> entry : sortedMap.entrySet()) {
            StringBuilder line = new StringBuilder("POL(");
            FunctionSymbol functionSymbol = entry.getKey();
            int arity = functionSymbol.getArity();

            StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
            if (arity > 0) {
                functionWithVars.append("(");
                for (int i = 1; i <= arity; i++) {
                    StringBuilder varBuf = new StringBuilder("X");
                    varBuf.append(eu.sub(Integer.valueOf(i).toString()));
                    functionWithVars.append(varBuf);
                    if (i < arity) {
                        functionWithVars.append(", ");
                    }
                }
                functionWithVars.append(")");
            }

            line.append(eu.bold(functionWithVars.toString()));
            line.append(") = ");
            line.append(entry.getValue().export(eu));

            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (eu instanceof HTML_Util) {
                line.append("<sup>&nbsp;</sup> <sub>&nbsp;</sub>");
            }
            rows.add(line.toString());
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public PlainLinearInterpretation specialize(Map<String, BigInteger> sol) {
        PlainLinearInterpretation res = new PlainLinearInterpretation();

        for (FunctionSymbol f : this.theMap.keySet()) {
            res.theMap.put(f, this.theMap.get(f).substituteParameters(sol));
        }
        return res;
    }

}
