package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.TermRelation;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Term next value (encapsulates a Term). To be used with the generic class Relation.
 * @author marinag
 *
 */
public class TermNextValue extends INextValue<TRSTerm> {

    public TermNextValue(final TRSTerm value) {
        super(value);
    }

    @Override
    public TRSTerm apply(final List<Pair<String, TRSTerm>> nextMap) {

        final HashMap<TRSVariable, TRSTerm> repMap = new HashMap<>();

        for (final Pair<String, TRSTerm> entry : nextMap) {
            repMap.put(TRSTerm.createVariable(entry.x), entry.y);
        }

        final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(repMap));

        return this.value.applySubstitution(sigma);
    }

    @Override
    public TermNextValue createNextValue(final String name) {
        return new TermNextValue(TRSTerm.createVariable(name));
    }

    @Override
    public Set<String> getVariables() {
        final Set<String> vars = new HashSet<>();

        for (final TRSVariable var : this.value.getVariables()) {
            vars.add(var.getName());
        }

        return vars;
    }



    public static List<Pair<String, TermNextValue>> getIdVector(final List<String> names) {
        final TermNextValue instance = new TermNextValue(TRSTerm.createVariable("x"));

        final List<Pair<String, TermNextValue>> items = new ArrayList<>();

        for (final String name : names) {
            items.add(new Pair<>(name, instance.createNextValue(name)));
        }

        return items;
    }

    @Override
    public INextValue<TRSTerm> rename(final Map<String, String> renaming) {
        return this;
    }

}
