package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.TermRelation;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author marinag
 * Relation over terms, allows flattening to linear relation represented by PolyRelation
 */
public class TermRelation extends GenericRelation<TRSTerm, TermNextValue> {

    protected TermRelation(final List<Pair<String, TermNextValue>> map) {
        super(map);
    }

    /**
     * @return an empty relation (identity)
     */
    public static TermRelation createIdentity(final List<String> variables) {
        return new TermRelation(TermNextValue.getIdVector(variables));
    }

    public static TermRelation createRelation(final List<Pair<TRSVariable, TRSTerm>> map) {
        final List<Pair<String, TermNextValue>> relMap = new ArrayList<>();

        for (final Pair<TRSVariable, TRSTerm> entry : map) {
            relMap.add(new Pair<>(entry.x.getName(), new TermNextValue(entry.y)));
        }

        return TermRelation.create(relMap);
    }

    public static TermRelation create(final List<Pair<String, TermNextValue>> relMap) {
        return new TermRelation(relMap);
    }

    public static TermRelation create() {
        return TermRelation.create(new ArrayList<Pair<String, TermNextValue>>());
    }

    public PolyRelation flatten(
        final Map<FunctionSymbol, Set<String>> fSymToVars,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp,
        final FreshNameGenerator ng)
    {
        final List<Pair<String, SimplePolynomial>> map = new ArrayList<>();

        for (final Pair<String, TermNextValue> p : this) {
            map.add(new Pair<>(p.x, p.y.getValue() == null ? null : TermTools.flattenSimplePolynomial(
                p.y.getValue(),
                fSymToVars,
                varsToFApp,
                ng)));
        }

        return PolyRelation.createRelation(map);
    }

    public TRSTerm apply(final TRSTerm t) {
        return super.apply(new TermNextValue(t));
    }

    public TermRelation compose(final TermRelation y) {
        final List<Pair<TRSVariable, TRSTerm>> tPairs = new ArrayList<>();

        for (final Pair<String, TRSTerm> entry : y.getTransitions()) {
            tPairs.add(new Pair<>(TRSTerm.createVariable(entry.x), this.apply(entry.y)));
        }

        return TermRelation.createRelation(tPairs);
    }
}