package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
@SuppressWarnings("serial")
public class FunctionSymbolReplacement extends LinkedHashMap<IFunctionSymbol<?>, ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>> {

    public static ImmutableList<Boolean> createRetainAllPositions(final IFunctionSymbol<?> fs) {
        final ArrayList<Boolean> res = new ArrayList<Boolean>(fs.getArity());

        for (int i = fs.getArity() - 1; i >= 0; i--) {
            res.add(Boolean.TRUE);
        }

        return ImmutableCreator.create(res);
    }

    public FunctionSymbolReplacement() {
    }

    @Override
    public ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> put(final IFunctionSymbol<?> fs, final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> replacement) {
        assert (fs != null && replacement != null) : "who does something like this?";
        assert (replacement.x.getArity() <= fs.getArity()) : "replacements have same or lower arity";
        assert (replacement.y.size() == fs.getArity()) : "retainedArguments size must be equal to fs arity";
        int retainedPosCount = 0;
        for (final Boolean val : replacement.y) {
            assert val != null : "null not allowed here";

            if (val) {
                retainedPosCount ++;
            }
        }
        assert (retainedPosCount == replacement.x.getArity()) : "retained arguments count must equal to replacement arity";
        return super.put(fs, replacement);
    }

    public int getNewPosition(final IFunctionSymbol<?> fs, final int position) {
        final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> fsReplacement = this.get(fs);
        if (fsReplacement != null) {
            if (!fsReplacement.y.get(position)) {
                return -1;
            }

            int newPos = 0;
            for (int i = position - 1; i >= 0; i--) {
                if (fsReplacement.y.get(i)) {
                    newPos++;
                }
            }

            return newPos;
        } else {
            return position;
        }

    }

    public FunctionSymbolReplacement compose(final FunctionSymbolReplacement functionSymbolReplacement) {
        final FunctionSymbolReplacement composed = new FunctionSymbolReplacement();

        for (final Map.Entry<IFunctionSymbol<?>, ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>> entry : this.entrySet()) {
            final ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>> composedReplacement =
                composed.get(entry.getValue().x);

            if (composedReplacement != null) {
                final List<Boolean> composedPositions = this.composePositions(entry.getValue().y, composedReplacement.y);
                entry.setValue(new ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>(
                        composedReplacement.x,
                        ImmutableCreator.create(composedPositions)));
            } else {
                composed.put(entry.getKey(), entry.getValue());
            }
        }

        for (final Map.Entry<IFunctionSymbol<?>, ImmutablePair<IFunctionSymbol<?>, ImmutableList<Boolean>>> entry : functionSymbolReplacement.entrySet()) {
            if (!this.containsKey(entry.getKey())) {
                composed.put(entry.getKey(), entry.getValue());
            }
        }

        return composed;
    }

    private List<Boolean> composePositions(final ImmutableList<Boolean> myPositions,
        final ImmutableList<Boolean> composed) {
        int pos = 0;
        final ArrayList<Boolean> result = new ArrayList<Boolean>(myPositions.size());
        for (int i = 0; i < myPositions.size(); i++) {
            if (myPositions.get(i)) {
                result.add(composed.get(pos));
                pos++;
            } else {
                result.add(Boolean.FALSE);
            }
        }

        return result;
    }

}
