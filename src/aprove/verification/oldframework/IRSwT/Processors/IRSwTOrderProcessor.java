package aprove.verification.oldframework.IRSwT.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IRSwT.Digraph.*;
import aprove.verification.oldframework.IRSwT.Engines.*;
import aprove.verification.oldframework.IRSwT.Orders.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IRSwT.Utils.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * A processor based on orders for integer rewrite systems with terms (IRSwT).
 * @author Matthias Hoelzel
 *
 */
public class IRSwTOrderProcessor extends Processor.ProcessorSkeleton {
    /** Some arguments. */
    private final Arguments arguments;

    /** Some arguments */
    public static class Arguments {
        /** Order your order here!*/
        public OrderType orderType = OrderType.INTERPRETATION;
    }

    /**
     * Constructor!
     */
    public IRSwTOrderProcessor() {
        this.arguments = new Arguments();
    }

    /**
     * Setter for the order type argument.
     * @param value some order type
     */
    public void setOrderType(final OrderType value) {
        this.arguments.orderType = value;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return Options.certifier.isNone() && obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        // 1. Get ready:
        assert obl instanceof IRSwTProblem : "Wrong obligation!";
        final IRSwTProblem irswt = (IRSwTProblem) obl;
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        final PartiallyComputedDigraph<IGeneralizedRule> terminationDigraph = irswt.getTerminationDigraph();
        final SymbolNamesCollector snc = new SymbolNamesCollector(irswt.getRules());

        // 2. Deduce the sorts:
        final SortAnalyzer sortAnalyzer = new SortAnalyzer(irswt.getRules());
        final SortDictionary sorts = sortAnalyzer.analyze();

        // 3. Synthesize a suitable order:
        final AbstractOrderEngine aoe = this.createOrderEngine(irswt.getRules(), sorts, snc, aborter, fng);
        final AbstractOrder order = aoe.getOrder();
        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        // 4. Generate the new problems:
        final LinkedList<IRSwTProblem> newProblems = new LinkedList<>();        
        
        // 4.2. Obtain the new rules:
        LinkedHashSet<IGeneralizedRule> newRulesSet1 = new LinkedHashSet<>(order.getRules());
        newRulesSet1.removeAll(order.getStrictOrientedRules());

        LinkedHashSet<IGeneralizedRule> newRulesSet2 = new LinkedHashSet<>(order.getRules());
        newRulesSet2.removeAll(order.getBoundedRules());

        if (newRulesSet1.isEmpty() && newRulesSet2.isEmpty()) {
            return ResultFactory.proved(new IRSwTOrderProof(order));
        }

        // 4.2. Prepare the termination digraphs:
        PartiallyComputedDigraph<IGeneralizedRule> termDigraph1;
        PartiallyComputedDigraph<IGeneralizedRule> termDigraph2;
        if (terminationDigraph != null) {
            termDigraph1 = terminationDigraph.getInducedSubgraph(newRulesSet1);
            termDigraph2 = terminationDigraph.getInducedSubgraph(newRulesSet2);

            // If these digraphs have only trivial SCCs,
            // then we do not need to solve this problem:
            termDigraph1.overestimate();
            if (termDigraph1.hasOnlyTrivialSCCs()) {
                newRulesSet1 = new LinkedHashSet<>();
                termDigraph1 = null;
            } else {
                termDigraph1.freeze();
            }

            termDigraph2.overestimate();
            if (termDigraph2.hasOnlyTrivialSCCs()) {
                newRulesSet2 = new LinkedHashSet<>();
                termDigraph2 = null;
            } else {
                termDigraph2.freeze();
            }
        } else {
            termDigraph1 = null;
            termDigraph2 = null;
        }

        if (newRulesSet1.isEmpty() && newRulesSet2.isEmpty()) {
            ResultFactory.proved(new IRSwTOrderProof(order));
        }

        if (newRulesSet1.containsAll(newRulesSet2)) {
            newProblems.add(new IRSwTProblem(ImmutableCreator.create(newRulesSet1), termDigraph1));
        } else if (newRulesSet2.containsAll(newRulesSet1)) {
            newProblems.add(new IRSwTProblem(ImmutableCreator.create(newRulesSet2), termDigraph2));
        } else {
            newProblems.add(new IRSwTProblem(ImmutableCreator.create(newRulesSet1), termDigraph1));
            newProblems.add(new IRSwTProblem(ImmutableCreator.create(newRulesSet2), termDigraph2));
        }

        return ResultFactory.provedAnd(newProblems, YNMImplication.EQUIVALENT, new IRSwTOrderProof(order));
    }

    /**
     * Create some order engine.
     * @param rules needs a set of rules to deal with
     * @param sorts needs a sort dictionary
     * @param snc sometimes we need a set of all symbols
     * @param abortion some aborter
     * @param fng some name generator
     * @return an order engine
     */
    private AbstractOrderEngine createOrderEngine(
        final Set<IGeneralizedRule> rules,
        final SortDictionary sorts,
        final SymbolNamesCollector snc,
        final Abortion abortion,
        final FreshNameGenerator fng)
    {
        switch (this.arguments.orderType) {
        case INTERPRETATION:
            return new InterpretationOrderEngine(
                rules,
                sorts,
                new FullSharingFactory<SMTLIBTheoryAtom>(),
                abortion,
                fng);
        default:
            return new SolverBasedTermOrderEngine(rules, sorts, this.arguments.orderType, abortion, fng);
        }
    }

    /**
     * A truly crackbrained proof!
     * @author Matthias Hoelzel
     */
    class IRSwTOrderProof extends DefaultProof {
        /** The order we found! */
        private final AbstractOrder order;

        /**
         * Based on an order we create a proof!
         * @param abstractOrder some order
         */
        public IRSwTOrderProof(final AbstractOrder abstractOrder) {
            this.order = abstractOrder;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            return this.order.export(eu);
        }
    }
}
