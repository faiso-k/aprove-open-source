package aprove.verification.complexity.CpxRntsProblem.Structures;

import java.util.ArrayList;
import java.util.List;

import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Processors.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.ComplexitySummary.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.IntTrsBoundProof.*;
import aprove.verification.oldframework.BasicStructures.*;


public class IntTrsBoundProofBuilder {
    private List<ProofStep> steps;
    private final CpxType type;

    public IntTrsBoundProofBuilder(CpxType cpxtype) {
        this.type = cpxtype;
        this.steps = new ArrayList<>();
    }

    public void add(FunctionSymbol goal, ComplexitySummary cpxres, CpxRntsProblem its, IntTrsBackend backend) {
        ProofStep step = new ProofStep();
        if (this.type == CpxType.Runtime) {
            assert cpxres.hasRuntime();
            step.cpx = cpxres.getRuntime();
            step.poly = cpxres.getRuntimePoly();
        } else {
            assert cpxres.hasSize();
            step.cpx = cpxres.getSize();
            step.poly = cpxres.getSizePoly();
        }
        step.goal = goal;
        step.its = its;
        step.backend = backend.getName();
        step.input = backend.getInput();
        step.proof = backend.getOutput();
        this.steps.add(step);
    }

    public IntTrsBoundProof buildProof() {
        return new IntTrsBoundProof(this.type,this.steps);
    }
}
