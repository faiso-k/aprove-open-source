package aprove.verification.oldframework.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 * An immutable and exportable Substitution.
 * @author cryingshadow
 * @version $Id$
 */
public interface ImmutableSubstitution extends Substitution, Immutable, Exportable {

    @SuppressWarnings("unchecked")
    @Override
    default String export(Export_Util eu) {
        ImmutableMap<? extends Variable, ? extends Expression> map = this.toMap();
        StringBuilder res = new StringBuilder();
        res.append(eu.export("["));
        Iterator<?> it = map.entrySet().iterator();
        if (it.hasNext()) {
            Map.Entry<? extends Variable, ? extends Expression> entry =
                (Map.Entry<? extends Variable, ? extends Expression>)it.next();
            res.append(eu.export(entry.getKey()));
            res.append(eu.export("/"));
            res.append(eu.export(entry.getValue()));
            while (it.hasNext()) {
                res.append(eu.export(", "));
                entry = (Map.Entry<? extends Variable, ? extends Expression>)it.next();
                res.append(eu.export(entry.getKey()));
                res.append(eu.export("/"));
                res.append(eu.export(entry.getValue()));
            }
        }
        res.append(eu.export("]"));
        return res.toString();
    }

    /**
     * @param sigma Some substitution as map.
     * @return The corresponding ImmutableSubstitution.
     */
    public static ImmutableSubstitution toSubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        final ImmutableMap<? extends Variable, ? extends Expression> map = ImmutableCreator.create(sigma);
        return
            new ImmutableSubstitution() {

                @Override
                public Expression substitute(Variable v) {
                    // cannot avoid code duplication since generics are just broken
                    if (map.containsKey(v)) {
                        return map.get(v);
                    }
                    return v;
                }

                @Override
                public ImmutableMap<? extends Variable, ? extends Expression> toMap() {
                    return map;
                }

            };
    }

    /**
     * @return A Map representation of this Substitution.
     */
    ImmutableMap<? extends Variable, ? extends Expression> toMap();

}
