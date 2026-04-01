package aprove.verification.idpframework.Algorithms.Matching;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;

/**
 *
 * @author MP
 */
public class TermMatchUnif<K> {

    private final ITerm<?> term;
    private final K key;
    private final ISubstitution matcher;

    public TermMatchUnif(final K key, final ITerm<?> term, final ISubstitution matcher) {
        this.key = key;
        this.term = term;
        this.matcher = matcher;
    }

    public ITerm<?> getTerm() {
        return this.term;
    }

    public K getKey() {
        return this.key;
    }

    public ISubstitution getMatcher() {
        return this.matcher;
    }

    @Override
    public String toString() {
        return this.key + ": " + this.term + this.matcher;
    }
}