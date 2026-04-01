package aprove.verification.oldframework.IRSwT.Digraph;

import java.util.*;

import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This class is responsible to compute the termination graph.
 * Its vertices are the rewrite rules of a given rewrite system,
 * while two rules u, v are connected via an arc iff it is possible
 * to apply v after applying u.
 * Since computation of this property requires an call of an SMT-Solver,
 * we try to avoid as many computations as possible. This is the reason why
 * we use partially computed digraphs.
 *
 * @author Matthias Hoelzel
 *
 */
public class TerminationDigraphComputation {
    /** Graph we are working on! */
    private final PartiallyComputedDigraph<IGeneralizedRule> digraph;

    /** Name generator */
    private final FreshNameGenerator fng;

    /** Aborter */
    private final Abortion aborter;

    /** Formula factory. */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /**
     * Constructor!
     * @param rules set of rules
     * @param fac formula factory
     * @param gen name generator
     * @param abortion aborter
     */
    public TerminationDigraphComputation(
        final Set<IGeneralizedRule> rules,
        final FormulaFactory<SMTLIBTheoryAtom> fac,
        final FreshNameGenerator gen,
        final Abortion abortion)
    {
        this.digraph = new PartiallyComputedDigraph<>(rules);
        this.factory = fac;
        this.fng = gen;
        this.aborter = abortion;
    }

    /**
     * Constructor!
     * @param start partially computed graph we start with
     * @param fac formula factory
     * @param gen name generator
     * @param abortion aborter
     */
    public TerminationDigraphComputation(
        final PartiallyComputedDigraph<IGeneralizedRule> start,
        final FormulaFactory<SMTLIBTheoryAtom> fac,
        final FreshNameGenerator gen,
        final Abortion abortion)
    {
        this.digraph = new PartiallyComputedDigraph<>(start);
        this.factory = fac;
        this.fng = gen;
        this.aborter = abortion;
    }

    /**
     * Computes the full termination digraph.
     * Of course, it ignores the parts, that have been already computed.
     * @return a fully computed digraph (in form of an partially computed digraph)
     * @throws AbortionException can be aborted
     */
    public PartiallyComputedDigraph<IGeneralizedRule> computeDigraph() throws AbortionException {
        final Set<IGeneralizedRule> rules = this.digraph.getVertices();
        for (final IGeneralizedRule rule1 : rules) {
            for (final IGeneralizedRule rule2 : rules) {
                if (!this.digraph.isEvaluated(rule1, rule2)) {
                    if (Options.certifier.isNone()) {
                        final Chaining chaining = new Chaining(rule1, rule2, this.fng, this.aborter);
                        final IGeneralizedRule chainedRule = chaining.applyChaining();
                        if (chainedRule != null) {
                            // Check whether it is impossible to use that rule:
                            final NonEmptinessChecking nec =
                                    new NonEmptinessChecking(chainedRule, this.factory, this.fng, this.aborter);
                            final YNM nonEmptinessResult = nec.checkNonEmptiness();
                            if (nonEmptinessResult == YNM.NO) {
                                // The rule condition is unsatisfiable? -> Disconnected!
                                this.digraph.disconnect(rule1, rule2);
                            } else {
                                // Otherwise we do not know a valid reason for not
                                // connecting these rules. Thus:
                                this.digraph.connect(rule1, rule2);
                            }
                        } else {
                            // When chaining fails, then the right side of the first rule
                            // does not unify with the left side of the second rule.
                            // Hence, these rules cannot occur consecutively.
                            this.digraph.disconnect(rule1, rule2);
                        }
                    } else {
                        // for CPF, just check root symbols
                        TRSTerm r1 = rule1.getRight();
                        if (r1.isVariable() || ((TRSFunctionApplication) r1).getRootSymbol().equals(rule2.getLeft().getRootSymbol())) {
                            this.digraph.connect(rule1, rule2);                            
                        } else {
                            this.digraph.disconnect(rule1, rule2);
                        }
                    }
                    

                    this.aborter.checkAbortion();
                }
            }
        }
        return this.digraph;
    }
}
