package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 *
 * Supplies the function hasBasicInstance(), which can check whether a
 * given set of class constraints has an instance without any further
 * class constraints.
 * This is only approximated, so there might be such an instance which
 * is not found.
 *
 * @author matraf
 *
 * @version $Id$
 *
 */
public class BasicInstanceChecker {

    private final ClassConstraintGraph ccg;
    private SimpleGraph<ClassConstraint, ClassConstraintRule> instDepGraph;
    private Set<ClassConstraintRule> cyclicRules;
    private Map<TyClassEntity, Collection<ClassConstraintRule>> class2rules;

    private long startedAt;
    private long maxRuntime;

    public BasicInstanceChecker(final ClassConstraintGraph ccg) {
        this.ccg = ccg;
        this.buildInstDepGraph();
    }

    /**
     * returns a node that represents the given ClassConstraint, such that every ClassConstraint occurs exactly once in the graph
     * @param cc A class constraint
     * @return A node that is already in the graph, or a new node if no such node existed in the graph yet (must be added to the graph outside)
     */
    private Node<ClassConstraint> getNodeFromCC(final ClassConstraint cc) {
        for (final Node<ClassConstraint> n : this.instDepGraph.getNodes()) {
            if (n.getObject().equivalentTo(cc)) {
                return n;
            }
        }
        return new Node<ClassConstraint>(cc);
    }

    /**
     * builds a Graph of the dependencies of instances based on the ClassConstraintRules in the ClassConstraintGraph this.ccg
     */
    private void buildInstDepGraph() {

        this.instDepGraph = new SimpleGraph<ClassConstraint, ClassConstraintRule>();
        for (final ClassConstraintRule ccr : this.ccg.getRules()) {
            final Node<ClassConstraint> patNode = this.getNodeFromCC(ccr.getPattern());
            this.instDepGraph.addNode(patNode);
            for (final ClassConstraint cc : ccr.getResults()) {
                final Node<ClassConstraint> resNode = this.getNodeFromCC(cc);
                this.instDepGraph.addNode(resNode);
                this.instDepGraph.addEdge(patNode, resNode, ccr);
            }
        }

        // look for cyclic rules
        for (final Node<ClassConstraint> n1 : this.instDepGraph.getNodes()) {
            for (final Node<ClassConstraint> n2 : this.instDepGraph.getNodes()) {
                if ((n1 != n2) && (n1.getObject().matches(n2.getObject()) != null)) {
                    this.instDepGraph.addEdge(n1, n2);
                }
            }
        }

        this.cyclicRules = new HashSet<ClassConstraintRule>();
        for (final Cycle<ClassConstraint> scc : this.instDepGraph.getSCCs()) {
            for (final Node<ClassConstraint> n : scc) {
                for (final Edge<ClassConstraintRule, ClassConstraint> e : this.instDepGraph.getOutEdges(n)) {
                    if ((e.getObject() != null) && (scc.contains(e.getEndNode()))) {
                        // this is not a matcher edge...
                        this.cyclicRules.add(e.getObject());
                    }
                }
            }
        }

        this.class2rules = new HashMap<TyClassEntity, Collection<ClassConstraintRule>>();
        for (final ClassConstraintRule ccr : this.ccg.getRules()) {
            final TyClassEntity tce = (TyClassEntity) ccr.getPattern().getTyClass().getEntity();
            if (!this.class2rules.containsKey(tce)) {
                final Set<ClassConstraintRule> tyClassRules = new HashSet<ClassConstraintRule>();
                this.class2rules.put(tce, tyClassRules);
            }
            this.class2rules.get(tce).add(ccr);
        }
    }

    /**
     * Checks whether a set of ClassConstraints has an instance that has no further ClassConstraints.
     * Please note that the result may be <code>false</code> if such an instance could not be found, it still might exist.
     * @param ccs The set of ClassConstraints to check
     * @return <code>true</code>, if there is an instance with no further class constraints; <code>false</code> otherwise
     */
    public boolean hasBasicInstance(final Set<ClassConstraint> ccs) {
        long now = System.currentTimeMillis();
        this.startedAt = now;
        this.maxRuntime = 5000; // 5 seconds

        final boolean res = this.hasBasicInstance(ccs, 5);

        now = System.currentTimeMillis() - now;

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            System.err.println("=========== Check Finished, result: " + res + " (took: " + (now / 1000.) + " seconds)");
        }

        return res;
    }

    /*
     * worker function for hasBasicInstance(Set<ClassConstraint>)
     * only the specified number of recursive rules are applied, everything thereafter is treated as not-satisfyable
     */
    private boolean hasBasicInstance(final Set<ClassConstraint> ccs, final int recurseDepth) {

        if (ccs.isEmpty()) {
            // No class constraints left => success
            return true;
        }

        if (recurseDepth <= 0) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_MATRAF) {
                System.err.println("---------- no depth left => Backtrack...");
            }

            // depth limit reached => failure
            return false;
        }

        if (System.currentTimeMillis() > this.startedAt + this.maxRuntime) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_MATRAF) {
                System.err.println("---------- maximal runtime exceeded...");
            }

            // exceeded maximum runtime => stop with failure
            return false;
        }

        final TyClassEntity tce = (TyClassEntity) ccs.iterator().next().getTyClass().getEntity();
        final Collection<ClassConstraintRule> rules = this.class2rules.get(tce);

        if (rules == null) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_MATRAF) {
                System.err.println("---------- no rules for this class.");
            }

            // there are no rules, i.e. there is no instance
            return false;
        }

        for (ClassConstraintRule ccr : rules) {
            if (this.cyclicRules.contains(ccr)) {
                continue; // try non-recursive rules first
            }

            ccr = ccr.freshVarCopy();

            final ClassConstraint cc = ccs.iterator().next();
            final HaskellSubstitution sigma = cc.unifies(ccr.getPattern());

            if (sigma != null) {
                final Set<ClassConstraint> ccs_new = new HashSet<ClassConstraint>();
                for (final ClassConstraint cc_new : ccs) {
                    if (cc_new != cc) {
                        // apply does Copy.deep
                        ccs_new.add(cc_new.apply(sigma));
                    }
                }
                for (final ClassConstraint cc_res : ccr.getResults()) {
                    // apply does Copy.deep
                    ccs_new.add(cc_res.apply(sigma));
                }
                // reduce the newly created constraints to normal form
                this.ccg.reduce(ccs_new);

                // XXX DEBUG
                if (aprove.Globals.DEBUG_MATRAF) {
                    System.err.println("Old CCs: " + ccs);
                    System.err.println("Narrowing ClassConstraint " + cc + " with non-recursive rule " + ccr + "...");
                    System.err.println("New CCs: " + ccs_new);
                }

                if (this.hasBasicInstance(ccs_new, recurseDepth)) {
                    return true;
                }
            }
        }

        // no luck => try recursive rules
        for (ClassConstraintRule ccr : rules) {
            if (!this.cyclicRules.contains(ccr)) {
                continue;
            }

            ccr = ccr.freshVarCopy();

            final ClassConstraint cc = ccs.iterator().next();
            final HaskellSubstitution sigma = cc.unifies(ccr.getPattern());

            if (sigma != null) {
                final Set<ClassConstraint> ccs_new = new HashSet<ClassConstraint>();
                for (final ClassConstraint cc_new : ccs) {
                    if (cc_new != cc) {
                        // apply does Copy.deep
                        ccs_new.add(cc_new.apply(sigma));
                    }
                }
                for (final ClassConstraint cc_res : ccr.getResults()) {
                    // apply does Copy.deep
                    ccs_new.add(cc_res.apply(sigma));
                }
                // reduce the newly created constraints to normal form
                this.ccg.reduce(ccs_new);

                // XXX DEBUG
                if (aprove.Globals.DEBUG_MATRAF) {
                    System.err.println("Old CCs: " + ccs);
                    System.err.println("Narrowing ClassConstraint " + cc + " with recursive rule " + ccr + "...");
                    System.err.println("New CCs: " + ccs_new);
                }

                if (this.hasBasicInstance(ccs_new, recurseDepth - 1)) {
                    return true;
                }
            }
        }

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            System.err.println("--------- no rules left => Backtrack...");
        }

        // no rules had success => failure
        return false;
    }

}
