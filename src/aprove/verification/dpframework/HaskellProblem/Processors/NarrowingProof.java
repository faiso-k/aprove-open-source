package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author Stephan Swiderski
 */
public class NarrowingProof extends Proof implements DOT_Able {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.TerminationProofs");
    String graph;
    private int startTermNumber;

    public NarrowingProof() {
    }

    public NarrowingProof(
        final HaskellProgram oldHaskellProgram,
        final Object trs,
        final String graph,
        final int startTermNumber)
    {
        super();
        this.name = "Narrowing";
        this.shortName = "Narrow";
        this.longName = "Narrowing";
        this.graph = graph;
        this.startTermNumber = startTermNumber;
    }

    public String getGraph() {
        return this.graph;
    }

    public void setGraph(final String graph) {
        this.graph = graph;
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(final Export_Util o) {

        // XXX DEBUG timing information
        final long startMillis = System.currentTimeMillis();

        this.startUp();
        this.result.append("Haskell To QDPs" + o.newline());
        //result.append("For non-termination analysis, all cycles are left out for which no instance without constraints could be found."+o.newline());
        if (o instanceof HTML_Util) {
            this.result.append("<textarea cols=\"80\" rows=\"25\">");
            this.result.append(this.graph);
            this.result.append("</textarea>");
        } else {
            this.result.append(o.export(this.graph));
        }

        // XXX DEBUG timing information
        if (aprove.Globals.DEBUG_MATRAF) {
            final long afterProofExportMillis = System.currentTimeMillis();
            System.err.println("Exporting the NarrowingProof took "
                + ((afterProofExportMillis - startMillis) / 1000d)
                + " sec");
        }

        return this.result.toString();
    };

    /**
     * Returns a BibTeX citation string for elements of this proof.
     */
    public String toBibTeX() {
        // No citations are given.
        return "";
    };

    public int getStartTermNumber() {
        return this.startTermNumber;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toDOT() {
        return this.graph;
    }

}
