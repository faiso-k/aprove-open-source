package aprove.verification.oldframework.Automata;

import java.util.*;

/**
 * An extension to classical regexps where words are accepted that match any
 * subregexp.
 * @author cotto
 * @param <X> the alphabet
 */
public final class RegexpOr<X> extends RegexpNAry<X> {
    /**
     * Just store the subexpressions.
     * @param args the subexpressions.
     */
    private RegexpOr(final Set<Regexp<X>> args) {
        super(args);
    }

    /**
     * @param <X> the alphabet
     * @param args the subexpressions
     * @return one+two+...
     */
    static <X> Regexp<X> create(final Collection<Regexp<X>> args) {
        final Set<Regexp<X>> result = new LinkedHashSet<Regexp<X>>();
        for (final Regexp<X> sub : args) {
            if (sub instanceof RegexpEmptyLanguage) {
                continue;
            }
            if (sub instanceof RegexpOr) {
                final RegexpOr<X> orSub = (RegexpOr<X>) sub;
                result.addAll(orSub.getSubs());
            }
            result.add(sub);
        }
        if (result.isEmpty()) {
            return RegexpEmptyLanguage.create();
        }
        if (result.size() == 1) {
            return result.iterator().next();
        }
        return new RegexpOr<X>(result);
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return super.toString("+");
    }
}
