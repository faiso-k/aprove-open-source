package aprove.solver.Engines;

import java.math.*;

import aprove.solver.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The engine for AProVE (termination prover) feat. AProVE (Diophantine solver)
 *
 * @author fuhs
 * @version $Id$
 */
public class APROVEEngine extends Engine {

    private String inFIFO = "/tmp/aprove.in";
    private String outFIFO = "/tmp/aprove.out";

    @Override
    public SearchAlgorithm getSearchAlgorithm(DefaultValueMap<String, BigInteger> ranges) {
        return AProVESearch.create(ranges, this.inFIFO, this.outFIFO);
    }

    /**
     * @param inFIFO the inFIFO to set
     */
    public void setInFIFO(String inFIFO) {
        this.inFIFO = inFIFO;
    }

    /**
     * @param outFIFO the outFIFO to set
     */
    public void setOutFIFO(String outFIFO) {
        this.outFIFO = outFIFO;
    }
}
