package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.List;
import java.util.Optional;

import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Interface for ITS backends using ITS comlexity analysis tools
 * (like KoAT, PUBS, CoFloCo...)
 *
 * @author mnaaf
 */
public interface IntTrsBackend {

    //run this backend, return true if execution (not the result) was successful
    public boolean run();

    //get backend data
    public String getName();
    public String getInput();
    public List<String> getOutput();

    //parse the result
    public ComplexityValue getComplexity();
    public Optional<SimplePolynomial> getPolynomialBound();

}
