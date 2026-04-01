package aprove.verification.complexity.CpxRntsProblem.Structures;

import java.util.List;
import java.util.Optional;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.ComplexitySummary.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;


public class IntTrsBoundProof extends CpxProof {

    static class ProofStep {
        ComplexityValue cpx;
        Optional<SimplePolynomial> poly;
        CpxRntsProblem its;
        List<String> proof;
        String input;
        String backend;
        FunctionSymbol goal;
    }

    private final List<ProofStep> proofSteps;
    private final CpxType type;

    IntTrsBoundProof(final CpxType type, final List<ProofStep> steps) {
        this.proofSteps = steps;
        this.type = type;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        StringBuilder s = new StringBuilder();
        for (ProofStep step : this.proofSteps) {
            s.append(o.linebreak());
            s.append(o.export("Computed "));
            if (type == CpxType.Runtime) {
                s.append("RUNTIME");
            } else {
                s.append("SIZE");
            }
            s.append(" bound using " + step.backend + " for: " + step.goal.export(o));
            s.append(o.linebreak());

            s.append("after applying outer abstraction to obtain an ITS,");
            s.append(o.linebreak());

            s.append("resulting in: ");
            s.append(step.cpx.export(o, "O"));
            s.append(o.escape(" with polynomial bound: "));
            if (step.poly.isPresent()) {
                s.append(step.poly.get().export(o));
            } else {
                s.append(o.escape("?"));
            }
            s.append(o.linebreak());
}
        return s.toString();
    }

}
