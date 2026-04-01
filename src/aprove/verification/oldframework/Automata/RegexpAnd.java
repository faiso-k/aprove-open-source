package aprove.verification.oldframework.Automata;

import java.util.*;

/**
 * An extension to classical regexps where only words are accepted that match
 * both subregexps.
 * @author cotto
 * @param <X> the alphabet
 */
public final class RegexpAnd<X> extends RegexpNAry<X> {
    /**
     * Just store the subexpressions.
     * @param args the subexpressions.
     */
    private RegexpAnd(final Set<Regexp<X>> args) {
        super(args);
    }

    /**
     * @param <X> the alphabet
     * @param args the subexpressions
     * @return one&two&...
     */
    static <X> Regexp<X> create(final Collection<Regexp<X>> args) {
        if (args.isEmpty()) {
            assert (false);
            return null;
        }
        final Set<Regexp<X>> result = new LinkedHashSet<Regexp<X>>();
        for (final Regexp<X> sub : args) {
            if (sub instanceof RegexpEmptyLanguage) {
                return sub;
            }
            if (sub instanceof RegexpAnd) {
                final RegexpAnd<X> andSub = (RegexpAnd<X>) sub;
                result.addAll(andSub.getSubs());
            }
            result.add(sub);
        }
        if (result.size() == 1) {
            return result.iterator().next();
        }
        return new RegexpAnd<X>(result);
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return super.toString("&");
    }
}
