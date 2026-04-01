package aprove.verification.complexity.Implications;

import aprove.verification.complexity.TruthValue.*;

public interface ComplexityComputation {

    public ComplexityComputation toAsymptotic();

    public ComplexityValue compute(ComplexityValue input);

}
