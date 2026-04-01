package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.RationalPolynomial.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class CIPI implements Exportable {
    private final ImmutableMap<FunctionSymbol, Pair<ImmutableList<TRSVariable>, RationalPolynomial>> interpretation;

    public CIPI(final ImmutableMap<FunctionSymbol, Pair<ImmutableList<TRSVariable>, RationalPolynomial>> interpretation) {
        this.interpretation = interpretation;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util eu) {
        StringBuilder sb = new StringBuilder();

        String I = eu.italic("I");

        sb.append("CIPI " + I + ":" + eu.linebreak());

        for (Entry<FunctionSymbol, Pair<ImmutableList<TRSVariable>, RationalPolynomial>> e : this.interpretation.entrySet()) {
            FunctionSymbol fs = e.getKey();
            ImmutableList<TRSVariable> args = e.getValue().x;
            RationalPolynomial term = e.getValue().y;
            sb.append(I + "(" + fs.export(eu) + "(");
            boolean first = true;
            for (TRSVariable var : args) {
                if (first) {
                    first = false;
                } else {
                    sb.append(",");
                }
                sb.append(var.toString());
            }
            sb.append(")) = ");
            sb.append(term.export(eu));
            sb.append(eu.linebreak());
        }
        return sb.toString();
    }

    public LinkedHashMap<CpxIntTupleRule, ComplexityValue> buildTupleUpdateMap(
        CpxIntTrsProblem obl,
        ImmutableSet<CpxIntTupleRule> strictTuples)
    {
        int k = 0;
        for (FunctionSymbol fs : obl.getG()) {
            k = Math.max(k, this.interpretation.get(fs).y.getMaximalPolynomialDegree());
        }

        LinkedHashMap<CpxIntTupleRule, ComplexityValue> updateMap = new LinkedHashMap<>();
        ComplexityValue p_k = k == 0 ? ComplexityValue.constant() : ComplexityValue.fixedDegreePoly(k);

        // TODO add case constant-bounded case, if it turns out to be useful

        for (CpxIntTupleRule rho : strictTuples) {
            if (p_k.compareTo(obl.getK().get(rho)) < 0) {
                updateMap.put(rho, p_k);
            }
        }

        return updateMap;
    }

    public RationalPolynomial interpretTerm(final TRSTerm t) {
        if (t.isVariable()) {
            return RationalPolynomial.createMonomial(1, t.getName());
        }

        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        if (CpxIntTermHelper.polySyms.contains(fs)) {
            if (CpxIntTermHelper.fUnaryMinus.equals(fs)) {
                return this.interpretTerm(fa.getArgument(0)).negate();
            }
            RationalPolynomial a0 = this.interpretTerm(fa.getArgument(0));
            RationalPolynomial a1 = this.interpretTerm(fa.getArgument(1));

            if (CpxIntTermHelper.fMul.equals(fs)) {
                return a0.multiply(a1);
            } else if (CpxIntTermHelper.fAdd.equals(fs)) {
                return a0.add(a1);
            } else if (CpxIntTermHelper.fSub.equals(fs)) {
                return a0.subtract(a1);
            }
        }

        BigInteger val = CpxIntTermHelper.getIntegerValue(fa);
        if (val != null) {
            return RationalPolynomial.createFromBigRational(new BigRational(val));
        }

        Pair<ImmutableList<TRSVariable>, RationalPolynomial> syminter = this.interpretation.get(fs);
        if (syminter == null) {
            throw new IllegalArgumentException("Unknown function symbol: " + fs.toString());
        }
        ImmutableList<TRSVariable> args = syminter.getKey();
        RationalPolynomial pol = syminter.getValue();
        Map<String, RationalPolynomial> subst = new LinkedHashMap<>();
        assert args.size() == fs.getArity();
        for (int i = 0, arity = fs.getArity(); i < arity; ++i) {
            String name = args.get(i).getName();
            TRSTerm ti = fa.getArgument(i);
            RationalPolynomial poli = this.interpretTerm(ti);
            subst.put(name, poli);
        }
        return pol.applySubstitution(subst);
    }

    public LinkedHashMap<CpxIntTupleRule, ComplexityValue> buildTupleUpdateMapUsingSizeBounds(
        CpxIntTrsProblem obl,
        Map<CallArgument, ComplexityValue> z,
        ImmutableSet<CpxIntTupleRule> strictTuples,
        ImmutableSet<CpxIntTupleRule> weakTuples)
    {
        ImmutableLinkedHashSet<FunctionSymbol> G = obl.getG();
        ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> K = obl.getK();
        LinkedHashSet<FunctionSymbol> startSyms = new LinkedHashSet<>();
        for (CpxIntTupleRule rho : IterableConcatenator.create(strictTuples, weakTuples)) {
            FunctionSymbol fs = rho.getRootSymbol();
            if (G.contains(fs)) {
                startSyms.add(fs);
            }
        }
        int k = 0;
        for (FunctionSymbol fs : startSyms) {
            k = Math.max(k, this.interpretation.get(fs).y.getMaximalPolynomialDegree());
        }

        CpxIntGraph g = obl.getDepGraph(AbortionFactory.create());

        ComplexityValue c = k == 0 ? ComplexityValue.constant() : ComplexityValue.fixedDegreePoly(k);

        for (CpxIntTupleRule rho : IterableConcatenator.create(strictTuples, weakTuples)) {
            for (Pair<CpxIntTupleRule, Integer> in : g.getIn(rho)) {
                CpxIntTupleRule xi = in.getKey();
                if (strictTuples.contains(xi) || weakTuples.contains(xi)) {
                    continue;
                }
                int i = in.getValue();
                FunctionSymbol f = xi.getRights().get(in.getValue()).getRootSymbol();
                ComplexityValue kxi = obl.getK().get(xi);
                assert kxi != null;
                ArrayList<ComplexityValue> args = new ArrayList<>();
                for (int a = 0, l = f.getArity(); a < l; ++a) {
                    CallArgument alpha = new CallArgument(xi, i, a);
                    ComplexityValue complexity = z.get(alpha);
                    assert complexity != null;
                    args.add(complexity);
                }

                ComplexityValue fc = this.applyComplexities(this.interpretation.get(f), args);
                c = c.max(kxi.mult(fc));
            }
        }

        // TODO add case constant-bounded case, if it turns out to be useful

        LinkedHashMap<CpxIntTupleRule, ComplexityValue> updateMap = new LinkedHashMap<>();
        for (CpxIntTupleRule rho : strictTuples) {
            if (c.compareTo(K.get(rho)) >= 0) {
                continue;
            }
            updateMap.put(rho, c);
        }
        return updateMap;
    }

    private ComplexityValue applyComplexities(
        Pair<ImmutableList<TRSVariable>, RationalPolynomial> pol_f,
        ArrayList<ComplexityValue> args)
    {
        ImmutableList<TRSVariable> vars = pol_f.x;
        assert args.size() == vars.size();
        LinkedHashMap<String, Integer> varComplexities = new LinkedHashMap<>();
        for (int i = 0, l = vars.size(); i < l; ++i) {
            ComplexityValue c = args.get(i);
            Integer d = null;
            if (c.isConstant()) {
                d = 0;
            } else if (c instanceof FixedDegreePoly) {
                d = ((FixedDegreePoly) c).getDegree();
            } else {
                assert c.isInfinite();
                d = null;
            }
            varComplexities.put(vars.get(i).getName(), d);
        }

        ComplexityValue m = ComplexityValue.constant();
        for (Monomial mon : pol_f.getValue()) {
            for (Entry<String, Integer> entry : mon.indefinitePart.getExponents().entrySet()) {
                String x = entry.getKey();
                int e = entry.getValue();
                assert e > 0;
                Integer vc = varComplexities.get(x);
                if (vc == null) {
                    return ComplexityValue.infinite();
                }
                int c = e * vc;
                m = m.max(c == 0 ? ComplexityValue.constant() : ComplexityValue.fixedDegreePoly(c));
            }
        }

        return m;
    }
}
