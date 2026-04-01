package aprove.verification.complexity.LowerBounds.ComplexityComputation;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Complexity.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;

public class RewriteSeqToComplexity {

    private RewriteSequence normalizationLog;
    private LowerBoundsToolbox toolbox;
    private int numberOfHypothesisApplications = 0;

    public RewriteSeqToComplexity(RewriteSequence normalizationLog, LowerBoundsToolbox toolbox) {
        this.normalizationLog = normalizationLog;
        this.toolbox = toolbox;
    }

    public Complexity execute() {
        PolynomialComplexity max = Complexity.ZERO;
        for (RewriteStep step : this.normalizationLog) {
            if (step.getRule() instanceof InductionHypothesis) {
                this.numberOfHypothesisApplications++;
                continue;
            }
            Complexity complexity = step.getComplexity(this.toolbox);
            assert !complexity.isExponential(): "Lemmas with exponential complexity must not be reused!";
            assert complexity.isPolynomial();
            PolynomialComplexity poly = (PolynomialComplexity) complexity;
            max = max.plus(poly);
        }
        if (this.numberOfHypothesisApplications >= 2) {
            return Complexity.EXPONENTIAL;
        } else if (this.numberOfHypothesisApplications == 0) {
            return max;
        } else {
            return max.times(Complexity.linear(this.toolbox.inductionVar.getName()));
        }
    }
}
