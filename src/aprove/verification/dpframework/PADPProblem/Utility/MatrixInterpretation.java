package aprove.verification.dpframework.PADPProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class MatrixInterpretation implements Exportable {

    private LinkedHashMap<FunctionSymbol, MatrixParamTerm> theMap;
    private Set<String> zCoeff;
    private Set<String> allCoeff;
    private BigInteger range;
    private int dim;
    private LinkedHashMap<FunctionSymbol, LinkedHashSet<Integer>> redpos;
    private Set<FunctionSymbol> pafuns;

    /**
     * Construct a MatrixInterpretation.
     */
    public MatrixInterpretation(List<PARule> p, Set<FunctionSymbol> funs, ImmutableMap<String, ImmutableList<String>> sortMap, ImmutableSet<FunctionSymbol> tupleSymbols, Map<FunctionSymbol, FunctionSymbol> defTup, BigInteger range, boolean noIntDependence, int dim) {
        this.theMap = new LinkedHashMap<FunctionSymbol, MatrixParamTerm>();
        this.zCoeff = new LinkedHashSet<String>();
        this.allCoeff = new LinkedHashSet<String>();
        this.range = range;
        this.dim = dim;
        this.pafuns = new LinkedHashSet<FunctionSymbol>();
        this.pafuns.add(FunctionSymbol.create("0", 0));
        this.pafuns.add(FunctionSymbol.create("1", 0));
        this.pafuns.add(FunctionSymbol.create("-", 1));
        this.pafuns.add(FunctionSymbol.create("+", 2));
        this.redpos = new LinkedHashMap<FunctionSymbol, LinkedHashSet<Integer>>();
        this.createRedpos(p, sortMap, defTup);
        this.createRedpos(funs, sortMap);
        this.addPredefined();
        for (FunctionSymbol f : funs) {
            String name = f.getName();
            if (name.equals("0") || name.equals("1") || name.equals("-") || name.equals("+")) {
                continue;
            } else {
                ImmutableList<String> sorts = sortMap.get(f.getName());
                if (sorts == null) {
                    sorts = sortMap.get(this.getDef(f, defTup).getName());
                }
                this.theMap.put(f, this.getMatry(f, sorts, tupleSymbols.contains(f), noIntDependence));
            }
        }
    }

    private void createRedpos(List<PARule> p, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> defTup) {
        for (PARule dp : p) {
            TRSFunctionApplication r = (TRSFunctionApplication) dp.getRight();
            FunctionSymbol f = r.getRootSymbol();
            LinkedHashSet<Integer> redposf = this.getRedPos(f);
            ImmutableList<String> sorts = sortMap.get(this.getDef(f, defTup).getName());
            int n = f.getArity();
            for (int i = 0; i < n; i++) {
                TRSTerm argi = r.getArgument(i);
                if (!sorts.get(i).equals("int") || !this.isPurePA(argi)) {
                    redposf.add(Integer.valueOf(i));
                }
            }
        }
    }

    private void createRedpos(Set<FunctionSymbol> funs, ImmutableMap<String, ImmutableList<String>> sortMap) {
        Set<FunctionSymbol> keyset = this.redpos.keySet();
        for (FunctionSymbol f : funs) {
            if (keyset.contains(f) || this.pafuns.contains(f)) {
                // noop
            } else {
                int n = f.getArity();
                List<String> sorts = sortMap.get(f.getName());
                LinkedHashSet<Integer> redposf = this.getRedPos(f);
                for (int i = 0; i < n; i++) {
                    if (sorts.get(i).equals("univ")) {
                        redposf.add(Integer.valueOf(i));
                    }
                }
            }
        }
    }

    private boolean isPurePA(TRSTerm t) {
        return this.pafuns.containsAll(t.getFunctionSymbols());
    }

    private LinkedHashSet<Integer> getRedPos(FunctionSymbol f) {
        LinkedHashSet<Integer> res = this.redpos.get(f);
        if (res == null) {
            res = new LinkedHashSet<Integer>();
            this.redpos.put(f, res);
        }
        return res;
    }

    private MatrixInterpretation() {
        this.theMap = new LinkedHashMap<FunctionSymbol, MatrixParamTerm>();
        this.zCoeff = new LinkedHashSet<String>();
        this.allCoeff = new LinkedHashSet<String>();
        this.range = BigInteger.ZERO;
        this.dim = 0;
    }

    private FunctionSymbol getDef(FunctionSymbol f, Map<FunctionSymbol, FunctionSymbol> defTup) {
        for (FunctionSymbol g : defTup.keySet()) {
            if (f.equals(defTup.get(g))) {
                return g;
            }
        }
        return null;
    }

    private void addPredefined() {
        FunctionSymbol zero = FunctionSymbol.create("0", 0);
        this.theMap.put(zero, new MatrixParamTerm(this.dim, 0));

        FunctionSymbol one = FunctionSymbol.create("1", 0);
        this.theMap.put(one, new MatrixParamTerm(this.dim, 1));

        FunctionSymbol minus = FunctionSymbol.create("-", 1);
        MatrixParamTerm zlpt = new MatrixParamTerm(this.dim, 0);
        MatrixParamTerm x1 = new MatrixParamTerm(this.dim, TRSTerm.createVariable("X_1"));
        this.theMap.put(minus, zlpt.minus(x1));

        FunctionSymbol plus = FunctionSymbol.create("+", 2);
        MatrixParamTerm x2 = new MatrixParamTerm(this.dim, TRSTerm.createVariable("X_2"));
        this.theMap.put(plus, x1.add(x2));
    }

    private MatrixParamTerm getMatry(FunctionSymbol f, ImmutableList<String> sorts, boolean isTuple, boolean noIntDependence) {
        int arity = f.getArity();
        String name = f.getName();
        boolean isUniv = (sorts.get(arity) == "univ");
        MatrixParamTerm[] vars = new MatrixParamTerm[arity];
        for (int i = 0; i < arity; i++) {
            vars[i] = new MatrixParamTerm(this.dim, TRSTerm.createVariable("X_" + (i + 1)));
        }
        List<String> coeff = this.getCoeff(name + "_" + (arity + 1));
        this.allCoeff.addAll(coeff);
        MatrixParamTerm res = new MatrixParamTerm(this.dim, coeff);
        for (int i = 0; i < arity; i++) {
            if (isTuple || !isUniv || !noIntDependence || (sorts.get(i) == "univ")) {
                // functions from F of sort univ may only depend on variables of sort univ
                List<List<String>> coeffs = this.getCoeffSquare(name + "_" + (i + 1));
                for (List<String> c : coeffs) {
                    this.allCoeff.addAll(c);
                }
                SimpleMatrix c_i = SimpleMatrix.createFull(coeffs);
                if (isTuple && !this.redpos.get(f).contains(Integer.valueOf(i))) {
                    // coefficient may be chosen from Z
                    for (List<String> c : coeffs) {
                        this.zCoeff.addAll(c);
                    }
                    c_i = c_i.plus(SimpleMatrix.create(this.dim, this.dim, this.range.negate()));
                    res = res.add(vars[i].mult(c_i));
                } else {
                    res = res.add(vars[i].mult(c_i));
                }
            }
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
     * Returns the coefficients that may be chosen from Z.
     */
    public Set<String> getZCoefficients() {
        return this.zCoeff;
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

    public Pair<Set<LinearTerm>, MatrixParamTerm> getInterpretation(PARule rule) {
        MatrixParamTerm mpt = this.getInterpretation(rule.getLeft()).minus(this.getInterpretation(rule.getRight()));
        Set<LinearTerm> conds = new LinkedHashSet<LinearTerm>();
        for (PAConstraint constr : rule.getConstraint()) {
            conds.addAll(this.getConstraints(constr));
        }
        return new Pair<Set<LinearTerm>, MatrixParamTerm>(conds, mpt);
    }

    public Pair<Set<LinearTerm>, MatrixParamTerm> getBoundInterpretation(PARule rule) {
        MatrixParamTerm mpt = this.getInterpretation(rule.getLeft());
        Set<LinearTerm> conds = new LinkedHashSet<LinearTerm>();
        for (PAConstraint constr : rule.getConstraint()) {
            conds.addAll(this.getConstraints(constr));
        }
        return new Pair<Set<LinearTerm>, MatrixParamTerm>(conds, mpt);
    }

    private Set<LinearTerm> getConstraints(PAConstraint cond) {
        Set<LinearTerm> res = new LinkedHashSet<LinearTerm>();
        TRSTerm l = cond.getLeft();
        TRSTerm r = cond.getRight();
        LinearTerm ll = new LinearTerm(l);
        LinearTerm lr = new LinearTerm(r);
        switch (cond.getType()) {
        case GTREQ:
            res.add(ll.minus(lr));
            break;
        case EQ:
            res.add(ll.minus(lr));
            res.add(lr.minus(ll));
            break;
        case GTR:
            TRSTerm[] t = new TRSTerm[0];
            LinearTerm one = new LinearTerm(TRSTerm.createFunctionApplication(FunctionSymbol.create("1", 0), t));
            res.add(ll.minus(lr.add(one)));
            break;
        default:
            throw new RuntimeException("Unknown type in LinearInterpretation.getConstraints");
        }
        return res;
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

    public MatrixInterpretation specialize(Map<String, BigInteger> sol) {
        MatrixInterpretation res = new MatrixInterpretation();

        for (FunctionSymbol f : this.theMap.keySet()) {
            res.theMap.put(f, this.theMap.get(f).substituteParameters(sol));
        }
        return res;
    }

}
