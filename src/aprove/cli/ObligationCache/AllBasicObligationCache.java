package aprove.cli.ObligationCache;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Logic.*;

public class AllBasicObligationCache extends BasicObligationCache {

    public AllBasicObligationCache() {
        super(new LinkedHashMap<BasicObligation, TruthValue>());
    }

}
