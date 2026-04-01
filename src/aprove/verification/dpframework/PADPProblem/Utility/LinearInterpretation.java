package aprove.verification.dpframework.PADPProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public class LinearInterpretation implements Exportable {

    private LinkedHashMap<FunctionSymbol, LinearParamTerm> theMap;
    private Set<String> zCoeff;
    private Set<String> allCoeff;
    private Set<String> monoCoeff;
    private BigInteger range;
    private LinkedHashMap<FunctionSymbol, LinkedHashSet<Integer>> redpos;
    private Set<FunctionSymbol> pafuns;

    /**
     * Construct a LinearInterpretation.
     */
    public LinearInterpretation(List<PARule> p, Set<FunctionSymbol> funs, ImmutableMap<String, ImmutableList<String>> sortMap, ImmutableSet<FunctionSymbol> tupleSymbols, Map<FunctionSymbol, FunctionSymbol> defTup, BigInteger range, boolean noIntDependence) {
        this.theMap = new LinkedHashMap<FunctionSymbol, LinearParamTerm>();
        this.zCoeff = new LinkedHashSet<String>();
        this.allCoeff = new LinkedHashSet<String>();
        this.monoCoeff = new LinkedHashSet<String>();
        this.range = range;
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
                this.theMap.put(f, this.getPoly(f, sorts, tupleSymbols.contains(f), noIntDependence));
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

    private LinearInterpretation() {
        this.theMap = new LinkedHashMap<FunctionSymbol, LinearParamTerm>();
        this.zCoeff = new LinkedHashSet<String>();
        this.allCoeff = new LinkedHashSet<String>();
        this.monoCoeff = new LinkedHashSet<String>();
        this.range = BigInteger.ZERO;
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
        this.theMap.put(zero, new LinearParamTerm(0));

        FunctionSymbol one = FunctionSymbol.create("1", 0);
        this.theMap.put(one, new LinearParamTerm(1));

        FunctionSymbol minus = FunctionSymbol.create("-", 1);
        LinearParamTerm zlpt = new LinearParamTerm(0);
        LinearParamTerm x1 = new LinearParamTerm(TRSTerm.createVariable("X_1"));
        this.theMap.put(minus, zlpt.minus(x1));

        FunctionSymbol plus = FunctionSymbol.create("+", 2);
        LinearParamTerm x2 = new LinearParamTerm(TRSTerm.createVariable("X_2"));
        this.theMap.put(plus, x1.add(x2));
    }

    private LinearParamTerm getPoly(FunctionSymbol f, ImmutableList<String> sorts, boolean isTuple, boolean noIntDependence) {
        int arity = f.getArity();
        String name = f.getName();
        boolean isUniv = (sorts.get(arity) == "univ");
        LinearParamTerm[] vars = new LinearParamTerm[arity];
        for (int i = 0; i < arity; i++) {
            vars[i] = new LinearParamTerm(TRSTerm.createVariable("X_" + (i + 1)));
        }
        String coeff = name + "_" + (arity + 1);
        this.allCoeff.add(coeff);
        LinearParamTerm res = new LinearParamTerm(coeff);
        for (int i = 0; i < arity; i++) {
            if (isTuple || !isUniv || !noIntDependence || (sorts.get(i) == "univ")) {
                // functions from F of sort univ may only depend on variables of sort univ
                coeff = name + "_" + (i + 1);
                this.allCoeff.add(coeff);
                if (this.redpos.get(f).contains(Integer.valueOf(i))) {
                    this.monoCoeff.add(coeff);
                }
                SimplePolynomial c_i = SimplePolynomial.create(coeff);
                if (isTuple && !this.redpos.get(f).contains(Integer.valueOf(i))) {
                    // coefficient may be chosen from Z
                    this.zCoeff.add(coeff);
                    c_i = c_i.plus(SimplePolynomial.create(this.range).times(SimplePolynomial.MINUS_ONE));
                    res = res.add(vars[i].mult(c_i));
                } else {
                    res = res.add(vars[i].mult(c_i));
                }
            }
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

    /**
     * Returns all coefficients that need to be positive for monotonicity.
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

    public Pair<Set<LinearTerm>, LinearParamTerm> getInterpretation(PARule rule) {
        LinearParamTerm lpt = this.getInterpretation(rule.getLeft()).minus(this.getInterpretation(rule.getRight()));
        Set<LinearTerm> conds = new LinkedHashSet<LinearTerm>();
        for (PAConstraint constr : rule.getConstraint()) {
            conds.addAll(this.getConstraints(constr));
        }
        return new Pair<Set<LinearTerm>, LinearParamTerm>(conds, lpt);
    }

    public Pair<Set<LinearTerm>, LinearParamTerm> getBoundInterpretation(PARule rule) {
        LinearParamTerm lpt = this.getInterpretation(rule.getLeft());
        Set<LinearTerm> conds = new LinkedHashSet<LinearTerm>();
        for (PAConstraint constr : rule.getConstraint()) {
            conds.addAll(this.getConstraints(constr));
        }
        return new Pair<Set<LinearTerm>, LinearParamTerm>(conds, lpt);
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

    public LinearParamTerm getInterpretation(Rule rule) {
        return this.getInterpretation(rule.getLeft()).minus(this.getInterpretation(rule.getRight()));
    }

    public LinearParamTerm getInterpretation(Equation eqn) {
        return this.getInterpretation(eqn.getLeft()).minus(this.getInterpretation(eqn.getRight()));
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder result = new StringBuilder("PA-Polynomial interpretation:\n");

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

    public LinearInterpretation specialize(Map<String, BigInteger> sol) {
        LinearInterpretation res = new LinearInterpretation();

        for (FunctionSymbol f : this.theMap.keySet()) {
            res.theMap.put(f, this.theMap.get(f).substituteParameters(sol));
        }
        return res;
    }

}
