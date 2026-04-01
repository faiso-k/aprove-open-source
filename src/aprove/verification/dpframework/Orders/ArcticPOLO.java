package aprove.verification.dpframework.Orders;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

public class ArcticPOLO implements QActiveOrder {

    private static final Pair<BigInteger, Boolean> arcticOne  = new Pair<BigInteger, Boolean>(BigInteger.ZERO, Boolean.FALSE);
    private static final Pair<BigInteger, Boolean> arcticZero = new Pair<BigInteger, Boolean>(BigInteger.ZERO, Boolean.TRUE);

    Map<FunctionSymbol, Pair<BigInteger, Boolean>> weightMap;
    Map<FunctionSymbol, List<Pair<BigInteger, Boolean>>> paramMap;

    Set<FunctionSymbol> symSet;

    private ArcticPOLO(final Map<FunctionSymbol, Pair<BigInteger, Boolean>> weightMap, final Map<FunctionSymbol, List<Pair<BigInteger, Boolean>>> paramMap, final Set<FunctionSymbol> symSet) {
        this.weightMap = weightMap;
        this.paramMap  = paramMap;
        this.symSet    = symSet;
    }

    public static ArcticPOLO create(final Map<FunctionSymbol, Pair<BigInteger, Boolean>> weightMap, final Map<FunctionSymbol, List<Pair<BigInteger, Boolean>>> paramMap, final Set<FunctionSymbol> symSet) {
        return new ArcticPOLO(weightMap, paramMap, symSet);
    }


    // Check if this ArcticPOLO satisfies the given QActiveCondition
    @Override
    public boolean checkQActiveCondition(final QActiveCondition condition) {
        final Set<? extends Set<Pair<FunctionSymbol, Integer>>> orSet = condition.getSetRepresentation();
        for (final Set<Pair<FunctionSymbol, Integer>> andSet : orSet) {
            boolean isOK = true;
            for (final Pair<FunctionSymbol, Integer> pair : andSet) {
                final FunctionSymbol sym = pair.x;
                final Integer i = pair.y;
                final Pair<BigInteger, Boolean> arcticNum = this.paramMap.get(sym).get(i);
                if (arcticNum.y) {
                    // This is -inf, but should be a finite number
                    isOK = false;
                    break;
                }
            }
            if (isOK) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) throws AbortionException {
        return this.solves(Constraint.<TRSTerm>create(s, t, OrderRelation.EQ));
    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) throws AbortionException {
        return this.solves(Constraint.<TRSTerm>create(s, t, OrderRelation.GR));
    }

    private Pair<BigInteger, Boolean> max(final Pair<BigInteger, Boolean> a, final Pair<BigInteger, Boolean> b) {
        if (a.y) {
            return b;
        }
        if (b.y) {
            return a;
        }
        if (a.x.compareTo(b.x) >= 0) {
            return a;
        }
        return b;
    }

    private Pair<BigInteger, Boolean> add(final Pair<BigInteger, Boolean> a, final Pair<BigInteger, Boolean> b) {
        if (a.y || b.y) {
            return ArcticPOLO.arcticZero;
        }
        final Pair<BigInteger, Boolean> result = new Pair<BigInteger, Boolean>(a.x.add(b.x), Boolean.FALSE);
        return result;
    }

    private void buildVarToValMap(final TRSTerm t,
            final Map<FunctionSymbol, List<Pair<BigInteger, Boolean>>> symToParamsMap,
            final Map<FunctionSymbol, Pair<BigInteger, Boolean>> symToConsMap,
            final Map<TRSVariable, Pair<BigInteger, Boolean>> varToValMap, final Pair<BigInteger, Boolean> constantVal,
            final Pair<BigInteger, Boolean> param) {

        if (t.isVariable()) {
            final TRSVariable vt = (TRSVariable)t;
            Pair<BigInteger, Boolean> values = varToValMap.get(vt);
            if (values == null) {
                values = ArcticPOLO.arcticZero;
            }

            values = this.max(param, values);
            varToValMap.put(vt, values);

        } else {
            final TRSFunctionApplication fat = (TRSFunctionApplication)t;
            final FunctionSymbol symt = fat.getRootSymbol();
            final Pair<BigInteger, Boolean> cons = symToConsMap.get(symt);
            final List<Pair<BigInteger, Boolean>> params = symToParamsMap.get(symt);
            // Collect constant value
            BigInteger iConst = cons.x;
            Boolean    bConst = cons.y;
            Pair<BigInteger, Boolean> newVal = this.add(param, new Pair<BigInteger, Boolean>(iConst, bConst));
            // This is ugly, but we have no call by reference :-/
            final Pair<BigInteger, Boolean> foo = this.max(constantVal, newVal);
            constantVal.x = foo.x;
            constantVal.y = foo.y;
            // Collect values for the parameters
            int i = 0;
            for (final Pair<BigInteger, Boolean> p : params) {
                iConst = p.x;
                bConst = p.y;
                newVal = this.add(param, new Pair<BigInteger, Boolean>(iConst, bConst));

                this.buildVarToValMap(fat.getArgument(i), symToParamsMap, symToConsMap, varToValMap, constantVal, newVal);
                i++;
            }
        }
    }


    // Check greater-equal on arctic numbers, where
    // a >= b iff either
    // b = -inf or
    // b != -inf, a != -inf and a >= b in natural numbers
    private boolean isGreaterEqual(final Pair<BigInteger, Boolean> a, final Pair<BigInteger, Boolean> b) {
        if (b.y) {
            return true;
        }
        if ((!a.y) && (a.x.compareTo(b.x) >= 0)) {
            return true;
        }
        return false;
    }

    // Check greater-then on arctic numbers, where
    // a > b iff either
    // b = -inf or
    // b != -inf, a != -inf and a > b in natural numbers
    private boolean isGreater(final Pair<BigInteger, Boolean> a, final Pair<BigInteger, Boolean> b) {
        if (b.y) {
            return true;
        }
        if ((!a.y) && (a.x.compareTo(b.x) > 0)) {
            return true;
        }
        return false;
    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) throws AbortionException {
        final List<Constraint<TRSTerm>> cList = new LinkedList<Constraint<TRSTerm>>();
        cList.add(c);
        final Set<TRSVariable> varSet = Constraint.getVariables(cList);
        return this.solves(c.x, c.y, c.z, varSet);
    }

    public boolean solves(final TRSTerm l, final TRSTerm r, final OrderRelation rel, final Set<TRSVariable> varSet) {
        // Collect values for l
        final Map<TRSVariable, Pair<BigInteger, Boolean>> varToValMapL = new LinkedHashMap<TRSVariable, Pair<BigInteger, Boolean>>();
        // This is arctic zero, but we need it for call by wannabe-reference
        final Pair<BigInteger, Boolean> constantValsL = new Pair<BigInteger, Boolean>(BigInteger.ZERO, Boolean.TRUE);
        this.buildVarToValMap(l, this.paramMap, this.weightMap, varToValMapL, constantValsL, ArcticPOLO.arcticOne);
        // Collect values for r
        final Map<TRSVariable, Pair<BigInteger, Boolean>> varToValMapR = new LinkedHashMap<TRSVariable, Pair<BigInteger, Boolean>>();
        // This is arctic zero, but we need it for call by wannabe-reference
        final Pair<BigInteger, Boolean> constantValsR = new Pair<BigInteger, Boolean>(BigInteger.ZERO, Boolean.TRUE);
        this.buildVarToValMap(r, this.paramMap, this.weightMap, varToValMapR, constantValsR, ArcticPOLO.arcticOne);

        switch(rel) {
        case GR:
            if (!this.isGreater(constantValsL, constantValsR)) {
                return false;
            }
            for (final TRSVariable v : varSet) {
                Pair<BigInteger, Boolean> left  = varToValMapL.get(v);
                Pair<BigInteger, Boolean> right = varToValMapR.get(v);
                if (left == null) {
                    left = ArcticPOLO.arcticZero;
                }
                if (right == null) {
                    right = ArcticPOLO.arcticZero;
                }
                if (!this.isGreater(left, right)) {
                    return false;
                }
            }
            return true;
        case GE:
            if (!this.isGreaterEqual(constantValsL, constantValsR)) {
                return false;
            }
            for (final TRSVariable v : varSet) {
                Pair<BigInteger, Boolean> left  = varToValMapL.get(v);
                Pair<BigInteger, Boolean> right = varToValMapR.get(v);
                if (left == null) {
                    left = ArcticPOLO.arcticZero;
                }
                if (right == null) {
                    right = ArcticPOLO.arcticZero;
                }
                if (!this.isGreaterEqual(left, right)) {
                    return false;
                }
            }
            return true;
        case EQ:
            return (this.solves(l, r, OrderRelation.GE, varSet) && this.solves(r, l, OrderRelation.GE, varSet));
        default:
            throw new UnsupportedOperationException("This relation type is not supported by ArcticPOLO");
        }
    }

    @Override
    public String export(final Export_Util o) {
        // TODO: This ArcticPOLO is not non-linear yet. If we get non-linear, these citations don't really proof arctic POLOs anymore - this must be changed then!
        final StringBuilder result = new StringBuilder("Polynomial interpretation "+o.cite(Citation.POLO)+" with arctic numbers"+o.cite(Citation.ARCTIC)+":"+o.newline());
        for (final FunctionSymbol sym: this.symSet) {
            final Pair<BigInteger, Boolean> consPair = this.weightMap.get(sym);
            final List<Pair<BigInteger, Boolean>> params = this.paramMap.get(sym);
            result.append("POL(");
            result.append(o.export(sym));
            final int arity = sym.getArity();
            if (arity > 0) {
                result.append ("(");
                boolean comma = false;
                for (int i = 1; i <= arity; i++) {
                    if (comma) {
                        result.append(", ");
                    }
                    comma = true;
                    result.append("x");
                    result.append(o.sub(""+i));
                }
                result.append(")");
            }
            result.append(") = ");
            if (consPair.y) {
                result.append("-I");
            } else {
                result.append(consPair.x);
                result.append("A");
            }
            int i = 0;
            for (final Pair<BigInteger, Boolean> p : params) {
                i++;
                result.append(" + ");
                if (p.y) {
                    result.append("-I");
                } else {
                    result.append(p.x);
                    result.append("A");
                }
                result.append(o.multSign());
                result.append("x");
                result.append(o.sub(""+i));
            }
            result.append(o.newline());
        }

        return result.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        throw new RuntimeException("no CPF export " + this.isCPFSupported());
    }

    @Override
    public String isCPFSupported() {
        return this.getClass().getCanonicalName();
    }

    private static final Element arcticToXML(final Document doc, final Pair<BigInteger, Boolean> value) {
        return XMLTag.createArcticInt(doc, value.y, value.x);
    }

}
