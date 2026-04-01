package aprove.verification.oldframework.Bytecode.Processors.ToSCC;

import java.lang.reflect.*;
import java.util.*;
import java.util.logging.*;

import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * This class holds the results of several preliminary analysis done on a
 * SCC of the finite interpretation graph. These results can then later be
 * accessed by the renderers encoding the SCC to an ITRS, allowing for a more
 * precise translation.
 *
 * @author Marc Brockschmidt
 */
public class SCCAnnotations {
    /**
     * Logger needed for output when any of the fancy reflection stuff fails:
     */
    private static final Logger LOGGER =
        Logger.getLogger("SCCAnnotations");

    /**
     * The SCC for which these annotations hold.
     */
    private final JBCGraph analysedSCC;

    /**
     * The set of analyses done on this SCC.
     */
    private final Set<SCCAnalysis> doneAnalyses;

    /**
     * @param scc the SCC to be annotated
     */
    public SCCAnnotations(final JBCGraph scc) {
        this.analysedSCC = scc;
        this.doneAnalyses = new LinkedHashSet<SCCAnalysis>();
    }

    /**
     * Given a class object, try to do the analysis specified by it.
     * @param requestedAnalysis Some class object referring to a SCCAnalysis.
     */
    public void doAnalysis(final Class<? extends SCCAnalysis> requestedAnalysis) {
        try {
            final Constructor<? extends SCCAnalysis> constr =
                requestedAnalysis.getConstructor(JBCGraph.class);
            this.doneAnalyses.add(constr.newInstance(this.analysedSCC));
        } catch (final Exception e) {
            //Inform user, run away:
            SCCAnnotations.LOGGER.log(Level.SEVERE,
                    "Could not perform SCC analysis " + requestedAnalysis.getCanonicalName() + ": " + e.getMessage());
            return;
        }
    }

    /**
     * @param searchedAnalysis Class object of some analysis
     * @return the analysis specified by <code>searchedAnalysis</code>, null
     *  if it wasn't done (yet).
     */
    public SCCAnalysis getAnalysis(final Class<? extends SCCAnalysis> searchedAnalysis) {
        for (final SCCAnalysis analysis : this.doneAnalyses) {
            if (analysis.getClass().equals(searchedAnalysis)) {
                return analysis;
            }
        }
        return null;
    }

    /**
     * @return set of performed analyses (DO NOT MODIFY, SHARES WITH INTERNAL STATE)
     */
    public Set<SCCAnalysis> getAnalyses() {
        return this.doneAnalyses;
    }

    /**
     * @param searchedAnalysis Class object of some analysis
     * @return true iff this analysis has been performed.
     */
    public boolean hasAnalysis(final Class<? extends SCCAnalysis> searchedAnalysis) {
        return (this.getAnalysis(searchedAnalysis) != null);
    }
}
