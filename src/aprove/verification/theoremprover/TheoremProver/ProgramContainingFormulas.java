package aprove.verification.theoremprover.TheoremProver;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;

public class ProgramContainingFormulas implements HTML_Able, LaTeX_Able {

    protected Program program;

    protected List<Formula> listOfFormulas;

    public ProgramContainingFormulas(Program program, List<Formula> listOfFormulas) {
        this.program = program;
        this.listOfFormulas    = listOfFormulas;
    }

    public List<Formula> getFormulas() {
        return this.listOfFormulas;
    }

    public Program getProgram() {
        return this.program;
    }

    @Override
    public String toHTML() {
        return this.program.toHTML();
    }

    @Override
    public String toLaTeX() {
        return this.program.toLaTeX();
    }

}