/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.AbstractInductionCalculus.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A class that contains the constraints for a QDPProblem. Offers additional
 * functions for using and updating the cache (for new QDPProblems).
 * do not change an existing ConstraintsCache
 * @author cotto
 *
 */
public class ConstraintsCache<R extends GeneralizedRule> implements Immutable {

    public static ConstraintsCache<Rule> emptyConstraintsCache = new ConstraintsCache<Rule>();

    final private Options options;
    final private int appliedInductions;

    /**
     * Storage for the constraints. The outer map's key is the DP problem, the
     * value is a map containing the associated constraints. For each
     * constraints the set of P rules is remembered that are used to generate
     * the constraint.
     */
    final private Pair<Map<R, Map<List<R>, List<Implication>>>, InductionCalculusProof> cache;

    private ConstraintsCache() {
        this.options = null;
        this.cache = null;
        this.appliedInductions = 0;
    }

    public boolean isEmpty() {
        return this.options == null;
    }

    public int getAppliedInductions() {
        return this.appliedInductions;
    }

    /**
     * Generate a new ConstraintsCache with given precomputed constraints.
     * @param newC The precomputed constraints.
     * @param options
     */
    public ConstraintsCache(
        final Pair<Map<R, Map<List<R>, List<Implication>>>, InductionCalculusProof> newC,
        Options options,
        int appliedInductions)
    {
        this.cache = newC;
        this.options = options;
        this.appliedInductions = appliedInductions;
    }

    public boolean needsRefresh(Options options) {
        return this == ConstraintsCache.emptyConstraintsCache || !this.options.equals(options);
    }

    /**
     * @return A map without information about the rules that are used for the
     * specific constraint.
     */
    public Map<R, List<Implication>> getProblemMap() {
        Map<R, List<Implication>> map = new LinkedHashMap<R, List<Implication>>();
        for (Map.Entry<R, Map<List<R>, List<Implication>>> entry : this.cache.x.entrySet()) {
            Map<List<R>, List<Implication>> innerMap = entry.getValue();
            int numSets = innerMap.size();
            List<Implication> newList = new ArrayList<Implication>(numSets * 2);
            for (List<Implication> list : entry.getValue().values()) {
                newList.addAll(list);
            }
            map.put(entry.getKey(), newList);
        }
        return map;
    }

    public InductionCalculusProof getProofForP(QDPProblem qdp) {
        return this.cache.y.createCopyForOutput(qdp);
    }

    public InductionCalculusProof getProofForP(IDPProblem idp) {
        return this.cache.y.createCopyForOutput(idp);
    }

    /*
     * count Implications with a non-empty conditions
     * @return number of Implications with non-empty conditions
     *         -1 if this chache is empty
     */
    public int countRealImplications() {
        int i = -1;
        if (!this.isEmpty()) {
            i = 0;
            for (Map.Entry<R, List<Implication>> entry : this.getProblemMap().entrySet()) {
                for (Implication imp : entry.getValue()) {
                    if (!imp.getConditions().isEmpty()) {
                        i++;
                    }
                }
            }
        }
        return i;
    }

    /**
     * Generate new constraints from a graph where some P rules might be
     * missing.
     * @param graph The graph of the new QDPProblem.
     * @return A new ConstraintsCache with less constraints, when the graph
     * contains less P rules.
     */
    public ConstraintsCache<Rule> fromGraph(final QDependencyGraph graph) {
        if (this == ConstraintsCache.emptyConstraintsCache) {
            return (ConstraintsCache<Rule>) this;
        }
        Set<Rule> graphP = graph.getP();
        return ((ConstraintsCache<Rule>) this).fromGraphP(graphP);
    }

    /**
     * Generate new constraints from a graph where some P rules might be
     * missing.
     * @param graph The graph of the new IDPProblem.
     * @return A new ConstraintsCache with less constraints, when the graph
     * contains less P rules.
     */
    /*
    public ConstraintsCache fromGraph(final IDependencyGraph graph) {
        if (this == emptyConstraintsCache) return this;
        Set<Node> graphP = graph.getNodes();
        return fromGraphP(graphP);
    }*/

    public ConstraintsCache<R> fromGraphP(Set<R> graphP) {
        Map<R, Map<List<R>, List<Implication>>> newC = new LinkedHashMap<R, Map<List<R>, List<Implication>>>();
        for (R rule : graphP) {

            Map<List<R>, List<Implication>> innerMap = this.cache.x.get(rule);
            assert (innerMap != null);
            for (Map.Entry<List<R>, List<Implication>> entry : innerMap.entrySet()) {
                List<R> pairs = entry.getKey();
                if (graphP.containsAll(pairs)) {
                    newC.put(rule, (Map<List<R>, List<Implication>>) innerMap);
                }
            }
        }
        return new ConstraintsCache<R>(new Pair<Map<R, Map<List<R>, List<Implication>>>, InductionCalculusProof>(
            newC,
            this.cache.y), this.options, this.appliedInductions);
    }

    public Options getOptions() {
        return this.options;
    }

}
