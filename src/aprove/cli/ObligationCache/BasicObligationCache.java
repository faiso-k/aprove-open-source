package aprove.cli.ObligationCache;

import java.util.*;

import aprove.*;
import aprove.prooftree.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Logic.*;

public abstract class BasicObligationCache {

    public static enum CACHE {OFF, ALL, LRU};
    public static BasicObligationCache oblCache;

    protected Map<BasicObligation, TruthValue> cache;

    protected BasicObligationCache(Map<BasicObligation, TruthValue> cache) {
        this.cache = cache;
    }

    public static final void init(CACHE mode, String cparam) {
        switch (mode) {
        case ALL:
            BasicObligationCache.oblCache =  new AllBasicObligationCache();
            break;
        case LRU:
            int limit = Integer.parseInt(cparam);
            BasicObligationCache.oblCache = new LRUBasicObligationCache(limit);
            break;
        case OFF:
            BasicObligationCache.oblCache = null;
        }
    }

    public TruthValue lookup(BasicObligation obl) {
        TruthValue value = this.cache.get(obl);
        if (Globals.DEBUG_NOWONDER) {
            System.err.println("Looking up \"+obl+\": "+value);
        }
        return value;
    }

    public void update(BasicObligation obl, TruthValue value) {
        TruthValue oldValue = this.cache.put(obl, value);
        if (Globals.useAssertions) {
            if (oldValue != null && !oldValue.equals(YNM.MAYBE)) {
                assert(oldValue.equals(value));
            }
        }
        if (Globals.DEBUG_NOWONDER) {
            System.err.println("Updating \"+obl+\": "+value);
        }
    }

    public final static class CacheTruthValueListener implements TruthValueListener {

        private BasicObligation obl;
        private BasicObligationCache cache;

        public CacheTruthValueListener(BasicObligationCache cache, BasicObligation obl) {
            this.cache = cache;
            this.obl = obl;
        }

        @Override
        public void truthValueChanged(TruthValue value, ObligationNode source) {
            if (value != YNM.MAYBE) {
                this.cache.update(this.obl, value);
            }
        }

    }

}
