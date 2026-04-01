package aprove.verification.oldframework.IRSwT.Processors.ExportProcessors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Turns an IRSwT into an QDP in a quite simple way:
 * We remove all integers to obtain a set of term rewrite rules
 * R', where always exactly one defined symbol occur at the root.
 * Then we set
 * P = R', R = E, Q = E [here E = the empty set!] to define the QDP (Q,P,R).
 * @author Matthias Hoelzel
 */
public class IRSwTToQDPProcessor extends Processor.ProcessorSkeleton {

    /**
     * If set to true, this processor will be unsuccessful when the
     * variable condition V(r) \subseteq V(l) does not hold in some
     * rule l -> r, which leads to a filtering.
     */
    private final boolean noSuccIfChanged;

    /** Constructor! */
    @ParamsViaArgumentObject
    public IRSwTToQDPProcessor(final Arguments arguments) {
        this.noSuccIfChanged = arguments.noSuccIfChanged;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl != null && obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded());
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSwTProblem irswt = (IRSwTProblem) obl;
        final SortDictionary sorts = new SortAnalyzer(irswt.getRules()).analyze();
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();

        final AbstractFilter filter = new RemoveIntFilter(irswt.getRules(), sorts, fng);
        final LinkedHashSet<IGeneralizedRule> noIntRules = filter.applyFilter();

        final AbstractFilter freeVarFilter = new FreeVarFilter(noIntRules);
        final LinkedHashSet<IGeneralizedRule> newRules = freeVarFilter.applyFilter();
        if (this.noSuccIfChanged && freeVarFilter.hasChanged()) {
            return ResultFactory.unsuccessful();
        }

        final LinkedHashSet<Rule> convertedRules = new LinkedHashSet<>();
        boolean killedCondition = false;
        for (final IGeneralizedRule iRule : newRules) {
            // Conditions of iRule are ignored:
            final TRSFunctionApplication left = iRule.getLeft();
            final TRSTerm right = iRule.getRight();

            killedCondition |= (iRule.getCondTerm() != null);

            if (!left.getVariables().containsAll(right.getVariables())) {
                return ResultFactory.unsuccessful();
            }

            final Rule rule = Rule.create(left, right);
            convertedRules.add(rule);
        }

        // R and Q are empty:
        final QTRSProblem qtrsProblem = QTRSProblem.create(ImmutableCreator.create(new TreeSet<Rule>()));
        final QDPProblem resultProblem = QDPProblem.create(ImmutableCreator.create(convertedRules), qtrsProblem, false);

        final YNMImplication impl;
        if (!filter.hasChanged() && !freeVarFilter.hasChanged() && !killedCondition) {
            impl = YNMImplication.EQUIVALENT;
        } else {
            impl = YNMImplication.SOUND;
        }

        return ResultFactory.proved(resultProblem, impl, new IRSwTToQDPProof());
    }

    /**
     * A truly horrendous proof!
     * @author Matthias Hoelzel
     */
    public class IRSwTToQDPProof extends DefaultProof {
        /** Constructor! */
        public IRSwTToQDPProof() {
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Removed the integers and created a QDP-Problem.";
        }
    }


    public static class Arguments {
        /** fail in case we have "free variables" on some rhs */
        public boolean noSuccIfChanged;
    }
}
