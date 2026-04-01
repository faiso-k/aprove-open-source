package aprove.verification.dpframework.PADPProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class PlainMatrixInterpretation implements Exportable {

    private LinkedHashMap<FunctionSymbol, MatrixParamTerm> theMap;
    private Set<String> allCoeff;
    private int dim;

    /**
     * Construct a PlainMatrixInterpretation.
     */
    public PlainMatrixInterpretation(int dim, Set<FunctionSymbol> funs) {
        this.dim = dim;
        this.theMap = new LinkedHashMap<FunctionSymbol, MatrixParamTerm>();
        this.allCoeff = new LinkedHashSet<String>();
        for (FunctionSymbol f : funs) {
            this.theMap.put(f, this.getMatry(f));
        }
    }

    private PlainMatrixInterpretation(int dim) {
        this.dim = dim;
        this.theMap = new LinkedHashMap<FunctionSymbol, MatrixParamTerm>();
        this.allCoeff = new LinkedHashSet<String>();
    }

    private MatrixParamTerm getMatry(FunctionSymbol f) {
        int arity = f.getArity();
        String name = f.getName();
        MatrixParamTerm[] vars = new MatrixParamTerm[arity];
        for (int i = 0; i < arity; i++) {
            vars[i] = new MatrixParamTerm(this.dim, TRSTerm.createVariable("X_" + (i + 1)));
        }
        List<String> coeff = this.getCoeff(name + "_" + (arity + 1));
        this.allCoeff.addAll(coeff);
        MatrixParamTerm res = new MatrixParamTerm(this.dim, coeff);
        for (int i = 0; i < arity; i++) {
            List<List<String>> coeffs = this.getCoeffSquare(name + "_" + (i + 1));
            for (List<String> c : coeffs) {
                this.allCoeff.addAll(c);
            }
            SimpleMatrix c_i = SimpleMatrix.createFull(coeffs);
            res = res.add(vars[i].mult(c_i));
        }
        return res;
    }

    private List<String> getCoeff(String name) {
        List<String> res = new Vector<String>();
        for (int i = 0; i < this.dim; i++) {
            res.add(name + "_" + i);
        }
        return res;
    }

    private List<List<String>> getCoeffSquare(String name) {
        List<List<String>> res = new Vector<List<String>>();
        for (int i = 0; i < this.dim; i++) {
            res.add(this.getCoeff(name + "_" + i));
        }
        return res;
    }

    /**
     * Returns all coefficients.
     */
    public Set<String> getCoefficients() {
        return this.allCoeff;
    }

    public MatrixParamTerm getInterpretation(TRSTerm t) {
        MatrixParamTerm res;
        if (t.isVariable()) {
            res = new MatrixParamTerm(this.dim, (TRSVariable) t);
        } else {
            TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            if (args.isEmpty()) {
                return this.theMap.get(fApp.getRootSymbol());
            }
            // compute the interpretations of the arguments
            int size = args.size();
            Map<TRSVariable, MatrixParamTerm> subst = new LinkedHashMap<TRSVariable, MatrixParamTerm>(size);
            for (int i = 0; i < size; i++) {
                TRSVariable argVar = TRSTerm.createVariable("X_" + (i + 1));
                MatrixParamTerm argPoly = this.getInterpretation(args.get(i));
                subst.put(argVar, argPoly);
            }
            // get the interpretation of the root symbol
            MatrixParamTerm tmp = this.theMap.get(fApp.getRootSymbol());
            // and plug the arg polys into the root poly
            res = tmp.substituteVariables(subst);
        }
        return res;
    }

    public MatrixParamTerm getInterpretation(PARule rule) {
        return this.getInterpretation(rule.getLeft()).minus(this.getInterpretation(rule.getRight()));
    }

    public MatrixParamTerm getInterpretation(Rule rule) {
        return this.getInterpretation(rule.getLeft()).minus(this.getInterpretation(rule.getRight()));
    }

    public MatrixParamTerm getInterpretation(Equation eqn) {
        return this.getInterpretation(eqn.getLeft()).minus(this.getInterpretation(eqn.getRight()));
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder result = new StringBuilder("Plain-Matrix interpretation:\n");

        int size = this.theMap.size();
        List<String> rows = new ArrayList<String>(size);

        Map<FunctionSymbol, MatrixParamTerm> sortedMap = new TreeMap<FunctionSymbol, MatrixParamTerm>(this.theMap);
        for (Map.Entry<FunctionSymbol, MatrixParamTerm> entry : sortedMap.entrySet()) {
            StringBuilder line = new StringBuilder("MAT(");
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

    public PlainMatrixInterpretation specialize(Map<String, BigInteger> sol) {
        PlainMatrixInterpretation res = new PlainMatrixInterpretation(this.dim);

        for (FunctionSymbol f : this.theMap.keySet()) {
            res.theMap.put(f, this.theMap.get(f).substituteParameters(sol));
        }
        return res;
    }

}
