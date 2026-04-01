package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;

import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;

/**
 *
 * @author Martin Pluecker
 */
public class ConditionMap<T> {

    private final Map<T, Itpf> conditions;
    private final ItpfFactory itpfFactory;
    private final FreshVarGenerator freshVarGenerator;

    public ConditionMap(final ItpfFactory itpfFactory, final FreshVarGenerator freshVarGenerator) {
        this.itpfFactory = itpfFactory;
        this.freshVarGenerator = freshVarGenerator;
        this.conditions = new LinkedHashMap<T, Itpf>();
    }

    public ConditionMap(final ItpfFactory itpfFactory,
            final FreshVarGenerator freshVarGenerator,
            final Map<T, Itpf> source) {
        this.itpfFactory = itpfFactory;
        this.freshVarGenerator = freshVarGenerator;
        this.conditions = new LinkedHashMap<T, Itpf>(source);
    }

    public Itpf get(final T edge) {
        return this.conditions.get(edge);
    }

    public Itpf putReplace(final T edge, final Itpf cond) {
        return this.conditions.put(edge, cond);
    }

    public Itpf putFalse(final T edge) {
        return this.conditions.put(edge, this.itpfFactory.createFalse());
    }

    public Itpf putAnd(final T edge, final Itpf cond) {
        Itpf combined = this.conditions.get(edge);
        if (combined == null) {
            combined = cond;
        } else {
            combined = this.itpfFactory.createAnd(this.freshVarGenerator, combined, cond);
        }
        return this.conditions.put(edge, combined);
    }

    public Itpf putOr(final T edge, final Itpf cond) {
        Itpf combined = this.conditions.get(edge);
        if (combined == null) {
            combined = cond;
        } else {
            combined = this.itpfFactory.createOr(this.freshVarGenerator, combined, cond);
        }
        return this.conditions.put(edge, combined);
    }

    public Set<Map.Entry<T, Itpf>> entrySet() {
        return this.conditions.entrySet();
    }

    public Set<T> keySet() {
        return this.conditions.keySet();
    }

    public Collection<Itpf> values() {
        return this.conditions.values();
    }

    public boolean isEmpty() {
        return this.conditions.isEmpty();
    }

    public Map<T, Itpf> getMap() {
        return this.conditions;
    }

}
