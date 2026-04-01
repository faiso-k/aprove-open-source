package aprove.verification.complexity.CdtProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;

/**
 * Complex Complexity Dependency Tuples problem.
 *
 * FIXME: Add documentation.
 */
public class ComplexCdtProblem extends DefaultBasicObligation {

    private final Set<ComplexCdtProblem> complexTodos;

    private final Set<CdtProblem> concreteTodos;

    private final boolean mult;

    /**
     * @param rules See {@link #rules} for constraints.
     */
    public ComplexCdtProblem(
        final Set<CdtProblem> concreteTodos,
        final Set<ComplexCdtProblem> complexTodos,
        final boolean mult)
    {
        super("ComplexCdtProblem", "Complex Complexity Dependency Tubles Problem");
        this.complexTodos = complexTodos;
        this.concreteTodos = concreteTodos;
        this.mult = mult;
        if (Globals.useAssertions) {
            assert (this.complexTodos != null && this.concreteTodos != null) : "todos may not be null!";
        }
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append(o.escape("Complex Complexity Dependency Tuples Problem"));
        sb.append(o.newline());
        sb.append(this.multiply() ? o.escape("MULTIPLY") : o.escape("MAX"));
        sb.append(o.set(this.getTodos(), Export_Util.RULES));
        sb.append(o.newline());
        return sb.toString();
    }

    public Set<ComplexCdtProblem> getComplexTodos() {
        return this.complexTodos;
    }

    public Set<CdtProblem> getConcreteTodos() {
        return this.concreteTodos;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        // TODO Auto-generated method stub
        return null;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Obligations.BasicObligation#getStrategyName()
     */
    @Override
    public String getStrategyName() {
        return null;
    }

    public Set<BasicObligation> getTodos() {
        final Set<BasicObligation> res = new LinkedHashSet<BasicObligation>();
        res.addAll(this.concreteTodos);
        res.addAll(this.complexTodos);
        return res;
    }

    public boolean isEmpty() {
        return this.getTodos().isEmpty();
    }

    public boolean multiply() {
        return this.mult;
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("Complex Complexity Dependency Tuples Problem\n");
        sb.append(this.multiply() ? "MULTIPLY" : "MAX");
        sb.append("\n");
        for (final BasicObligation obl : this.getTodos()) {
            sb.append(obl.toString());
            sb.append("\n");
        }
        return sb.toString();
    }

}
