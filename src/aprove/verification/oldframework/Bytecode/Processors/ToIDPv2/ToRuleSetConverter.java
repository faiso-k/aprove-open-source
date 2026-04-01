package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * Parent of workers converting edges in TerminationGraphs to sets of IRules.
 */
public abstract class ToRuleSetConverter implements Runnable {
    /**
     * The aborter.
     */
    private final Abortion aborter;

    /**
     * The instance handling the actual conversion to rules.
     */
    private final RuleCreator ruleCreator;

    /**
     * The resulting rule set.
     */
    private Collection<IRule> result;

    /**
     * A flag indicating if the conversion is finished.
     */
    private boolean isConverted;

    /**
     * @param abort aborter we are supposed to check for abortions.
     * @param ruleC an instance handling the actual conversion to rules.
     */
    public ToRuleSetConverter(final Abortion abort, final RuleCreator ruleC) {
        this.aborter = abort;
        this.ruleCreator = ruleC;
        this.isConverted = false;
    }

    /**
     * @param converted the isConverted to set
     */
    public void setConverted(final boolean converted) {
        this.isConverted = converted;
    }

    /**
     * @return the aborter
     */
    public Abortion getAborter() {
        return this.aborter;
    }

    /**
     * @param res the result to set
     */
    public void setResult(final Collection<IRule> res) {
        this.result = res;
    }

    /**
     * Wait for this conversion to finish.
     * @throws InterruptedException when processing was interrupted.
     */
    public synchronized void waitForConversion() throws InterruptedException {
        while (!this.isConverted) {
            this.wait();
        }
    }

    /**
     * @return the rules resulting from the converted graph.
     */
    public synchronized Collection<IRule> getResult() {
        assert (this.isConverted) : "Trying to access result before computation finished";
        return this.result;
    }

    /**
     * Execute this exporter.
     */
    @Override
    public synchronized void run() {
        try {
            this.convert();
            this.isConverted = true;
        } catch (final AbortionException e) {
            this.isConverted = false;
        }
        this.notifyAll();
    }

    public abstract Collection<Edge> getEdges();

    /**
     * Actually perform the scheduled conversion.
     *
     * @throws AbortionException happens when we are asked to stop.
     */
    public void convert() throws AbortionException {
        /*
         * We want to generate a set of rules for each of the edges in this
         * graph.
         */
        final Collection<IRule> rules = new LinkedHashSet<IRule>();

        for (final Edge e : this.getEdges()) {
            this.getAborter().checkAbortion();

            //Do not encode the edge to an empty box.
            if (e.getEnd().getState().callStackEmpty()) {
                continue;
            }

            rules.addAll(this.ruleCreator.convert(e, false, true));
        }

        if (Globals.useAssertions) {
            final Map<String, Integer> arityMap = new LinkedHashMap<String, Integer>();
            for (final IRule rule : rules) {
                final Collection<ITerm<?>> subterms = new LinkedList<ITerm<?>>();
                subterms.addAll(rule.getLeft().getSubTerms());
                subterms.addAll(rule.getRight().getSubTerms());
                for (final ITerm<?> t : subterms) {
                    if (t instanceof IFunctionApplication) {
                        final IFunctionSymbol<?> fa = ((IFunctionApplication<?>) t).getRootSymbol();
                        final String name = fa.getName();
                        if (arityMap.containsKey(name)) {
                            assert (arityMap.get(name) == fa.getArity()) :
                                "Symbol " + name + " appears with arity "
                                + arityMap.get(name) + " and "
                                + fa.getArity() + "!";
                        }
                        arityMap.put(name, fa.getArity());
                    }
                }
            }
        }

        this.setResult(rules);
        this.setConverted(true);
    }
}
