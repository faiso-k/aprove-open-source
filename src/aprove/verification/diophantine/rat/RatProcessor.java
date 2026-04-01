package aprove.verification.diophantine.rat;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 *
 * @author bearperson
 * @version $Id$
 */
public class RatProcessor extends Processor.ProcessorSkeleton {

    private final OPCSolver<? extends GPolyCoeff> solver;

    @ParamsViaArguments("Solver")
    public RatProcessor(OPCSolver<? extends GPolyCoeff> solver) {
        this.solver = solver;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        // If somebody calls this, he probably doesn't know what this is about.
        return false;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        // If somebody calls this, he probably doesn't know what this is about.
        return null;
    }

    public OPCSolver<? extends GPolyCoeff> getSolver() {
        return this.solver;
    }
}
