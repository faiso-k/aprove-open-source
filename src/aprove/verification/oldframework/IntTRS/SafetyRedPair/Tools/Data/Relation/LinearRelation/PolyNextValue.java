package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation;

import java.util.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author marinag
 * Polynomial next value (encapsulating a SimplePolynomial)
 */
public class PolyNextValue extends INextValue<SimplePolynomial> {

    public PolyNextValue(final SimplePolynomial value) {
        super(value);
    }

    @Override
    public SimplePolynomial apply(final List<Pair<String, SimplePolynomial>> nextMap) {

        final HashMap<TRSVariable, TRSTerm> repMap = new HashMap<>();

        for (final Pair<String, SimplePolynomial> entry : nextMap) {
            if (entry.y == null) {
                if (this.value.getVariables().contains(entry.x)) {
                    return null;
                }
            } else {
                repMap.put(TRSTerm.createVariable(entry.x), entry.y.toTerm());
            }
        }

        final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(repMap));

        try {
            return TermTools.getSimplePolynomial(this.value.toTerm().applySubstitution(sigma));
        } catch (final UnsupportedException e) {
            throw new RuntimeException();
        }
    }

    @Override
    public PolyNextValue createNextValue(final String name) {
        return new PolyNextValue(SimplePolynomial.create(name));
    }

    @Override
    public Set<String> getVariables() {
        if (this.getValue() == null) {
            return new HashSet<String>();
        }

        return this.getValue().getVariables();
    }

    public static List<Pair<String, PolyNextValue>> getIdVector(final List<String> names) {
        final PolyNextValue instance = new PolyNextValue(SimplePolynomial.create("x"));

        final List<Pair<String, PolyNextValue>> items = new ArrayList<>();

        for (final String name : names) {
            items.add(new Pair<>(name, instance.createNextValue(name)));
        }

        return items;
    }

    @Override
    public INextValue<SimplePolynomial> rename(final Map<String, String> renaming) {
        return new PolyNextValue(this.value.replace(renaming));
    }
}
