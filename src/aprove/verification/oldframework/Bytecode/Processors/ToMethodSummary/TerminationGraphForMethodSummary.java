package aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

public class TerminationGraphForMethodSummary extends JBCTerminationGraphProblem {

    private MethodSummaryBuilder.Task task;

    public TerminationGraphForMethodSummary(TerminationGraph graphParam, MethodSummaryBuilder.Task task) {
        super(graphParam);
        this.task = task;
    }

    @Override
    public String export(Export_Util o) {
        return task + o.linebreak() + super.export(o);
    }



    public MethodSummaryBuilder.Task getTask() {
        return task;
    }
}
