package aprove.verification.oldframework.IntTRS.BoundedInts;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * This processor takes an intTRS and returns a bounded intTRS where everything
 * is casted to signed 32-bit-integers. This is used for debugging purposes,
 * because it generates some bounded intTRS to play with.
 * @author Matthias Hoelzel
 */
public class IntTRSTo32BitIntTRS extends Processor.ProcessorSkeleton {
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
        final IRSwTProblem kp = (IRSwTProblem) obl;

        final ImmutableSet<IGeneralizedRule> rules = kp.getRules();
        final Set<IGeneralizedRule> newRules = new LinkedHashSet<>(rules.size());

        for (final IGeneralizedRule rule : rules) {
            final IGeneralizedRule newRule = this.transformRule(rule);
            newRules.add(newRule);
        }

        final BoundInformation bi = this.generateBoundInformation(newRules);

        return ResultFactory.proved(
            new BoundedIntTRSProblem(ImmutableCreator.create(newRules), bi),
            YNMImplication.SOUND,
            new IntTRSTo32BitIntTRSProof());
    }

    /**
     * Generates some bound information.
     * @param rules current rules
     * @return BoundInformation: every variable is 32-Bit!
     */
    private BoundInformation generateBoundInformation(final Set<IGeneralizedRule> rules) {
        final LinkedHashMap<IGeneralizedRule, ImmutableLinkedHashMap<TRSVariable, IntegerType>> boundInfoMap =
            new LinkedHashMap<>(rules.size());
        for (final IGeneralizedRule rule : rules) {
            final Set<TRSVariable> ruleVars = rule.getVariables();
            final Set<TRSVariable> condVars = rule.getCondVariables();

            final LinkedHashMap<TRSVariable, IntegerType> domains = new LinkedHashMap<>(ruleVars.size() + condVars.size());
            for (final TRSVariable v : ruleVars) {
                domains.put(v, IntegerType.I32);
            }
            for (final TRSVariable v : condVars) {
                domains.put(v, IntegerType.I32);
            }
            boundInfoMap.put(rule, ImmutableCreator.create(domains));
        }
        return new BoundInformation(ImmutableCreator.create(boundInfoMap));
    }

    /**
     * Transforms a rule into a bounded rule.
     * @param rule some IGeneralizedRule
     * @return another IGeneralizedRule
     */
    private IGeneralizedRule transformRule(final IGeneralizedRule rule) {
        final TRSFunctionApplication left = rule.getLeft();
        final TRSFunctionApplication right = (TRSFunctionApplication) rule.getRight();
        final TRSTerm condition = rule.getCondTerm() == null ? ToolBox.buildTrue() : rule.getCondTerm();
        // Transform the arguments:
        final ImmutableList<TRSTerm> rightArgs = right.getArguments();
        final ArrayList<TRSTerm> newRightArgs = new ArrayList<>();
        for (final TRSTerm arg : rightArgs) {
            newRightArgs.add(
                TRSTerm.createFunctionApplication(
                    BoundedSymbolFactory.createCastSymbol(32, true),
                    arg
                )
            );
        }
        final TRSFunctionApplication newRightSide =
            TRSTerm.createFunctionApplication(right.getRootSymbol(), newRightArgs);
        // Transform the constraints:
        final TRSTerm newCondition = this.transformCondTerm(condition, IDPPredefinedMap.DEFAULT_MAP);
        return IGeneralizedRule.create(left, newRightSide, newCondition);
    }

    /**
     * Transforms a given condition into a valid 32-Bit-condition.
     * @param condition some condition term
     * @param predefMap some predefined map
     * @return transformed condition term
     */
    private TRSTerm transformCondTerm(final TRSTerm condition, final IDPPredefinedMap predefMap) {
        assert (condition != null && !condition.isVariable()) : "Strange condition: " + condition;
        final TRSFunctionApplication condFunc = (TRSFunctionApplication) condition;
        final FunctionSymbol sym = condFunc.getRootSymbol();
        if (predefMap.isBooleanTrue(sym) || predefMap.isBooleanFalse(sym)) {
            return condition;
        } else if (predefMap.isLand(sym) || predefMap.isLor(sym) || predefMap.isLnot(sym)) {
            final ImmutableList<TRSTerm> args = condFunc.getArguments();
            final ArrayList<TRSTerm> newArgs = new ArrayList<>(args.size());
            for (final TRSTerm arg : args) {
                newArgs.add(this.transformCondTerm(arg, predefMap));
            }
            return TRSTerm.createFunctionApplication(sym, newArgs);
        } else {
            assert sym.getArity() == 2 : "Expected some symbol of arity 2, but found: " + sym;
            final ImmutableList<TRSTerm> args = condFunc.getArguments();
            final ArrayList<TRSTerm> newArgs = new ArrayList<>(args.size());
            for (int i = 0; i <= 1; i++) {
                newArgs.add(
                    TRSTerm.createFunctionApplication(
                        BoundedSymbolFactory.createCastSymbol(32, true),
                        args.get(i)
                    )
                );
            }
            return TRSTerm.createFunctionApplication(sym, newArgs);
        }
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me)
     */
    class IntTRSTo32BitIntTRSProof extends DefaultProof {
        /** Create the proof. */
        public IntTRSTo32BitIntTRSProof() {
            super();
            this.shortName = "32BitProcessor";
            this.longName = "IntTRSTo32BitIntTRS";
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            return "Everything is now in 32-bit range!";
        }
    }
}
