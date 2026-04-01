package aprove.verification.oldframework.IntTRS;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class IntTRSFreeVarFilter extends Processor.ProcessorSkeleton {
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSwTProblem kittelProblem = (IRSwTProblem) obl;

        final ImmutableSet<IGeneralizedRule> rules = kittelProblem.getRules();

        final Set<GeneralizedRule> gRules =
            IGeneralizedRule.removeConditions(
                TerminationSCCToIDPv1Processor.filterFreeVarFromCond(rules, IDPPredefinedMap.DEFAULT_MAP, true),
                true);

        final Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>, Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>, Collection<Rule>> resultTriple =
            FreeVariableTermRemover.processRulePair(
                gRules,
                Collections.<GeneralizedRule>emptySet(),
                IDPPredefinedMap.DEFAULT_MAP,
                true,
                true,
                Integer.MAX_VALUE);

        if (resultTriple != null) {
            final Set<IGeneralizedRule> newRules = TerminationSCCToIDPv1Processor.readdConditions(resultTriple.x.x);

            if (IntTRSFreeVarFilter.haveSameRules(newRules, rules)) {
                final IRSwTProblem newProblem = new IRSwTProblem(ImmutableCreator.create(newRules));
                final IntTRSFreeVarFilterProof proof = new IntTRSFreeVarFilterProof(new RuleSet(resultTriple.z));
                return ResultFactory.proved(newProblem, YNMImplication.SOUND, proof);
            }
        }

        return ResultFactory.unsuccessful();
    }

    /**
     * @param a a set of rules
     * @param b another set of rules
     * @return true if the both sets contain the same rules (modulo variable
     * renaming)
     */
    public static boolean haveSameRules(final Set<IGeneralizedRule> a, final Set<IGeneralizedRule> b) {
        nextARule: for (final IGeneralizedRule aRule : a) {
            final IGeneralizedRule aStdRule = aRule.getWithRenumberedVariables("x");
            for (final IGeneralizedRule bRule : b) {
                final IGeneralizedRule bStdRule = bRule.getWithRenumberedVariables("x");
                if (aStdRule.equals(bStdRule)) {
                    continue nextARule;
                }
            }
            return false;
        }
        return true;
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me), Marc Brockschmidt
     */
    public class IntTRSFreeVarFilterProof extends DefaultProof {
        private final RuleSet filterRules;

        public IntTRSFreeVarFilterProof(final RuleSet filterR) {
            this.filterRules = filterR;
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Filtered free variables in intTRS. Removed arguments according to the following rules: ");
            sb.append(o.indent(this.filterRules.export(o)));
            sb.append(o.linebreak());
            return sb.toString();
        }
    }
}
