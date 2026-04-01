package aprove.cli.ObligationCache;

import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class LRUBasicObligationCache extends BasicObligationCache {

    public LRUBasicObligationCache(int limit) {
        super(new LRUCache<BasicObligation, TruthValue>(limit));
    }

}
