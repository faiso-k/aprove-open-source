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
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Transforms a bounded integer rewrite system into a normal one.
 * @author Matthias Hoelzel
 */
public class BoundedIntTRSToIntTRSProcessor extends Processor.ProcessorSkeleton {
    /** A class for the arguments */
    public static class Arguments {
        /** Specifies how many over-/underflows are corrected. */
        public int inlineLimit = 3;
    }

    /** Stores the arguments. */
    private final Arguments arguments;

    /**
     * A constructor.
     */
    public BoundedIntTRSToIntTRSProcessor() {
        this.arguments = new Arguments();
    }

    /**
     * A constructor.
     * @param args Arguments for this processor.
     */
    public BoundedIntTRSToIntTRSProcessor(final Arguments args) {
        this.arguments = args;
    }

    /**
     * Setter for the argument "inlineLimit".
     * @param value int
     */
    public void setSimplifyProblem(final int value) {
        this.arguments.inlineLimit = value;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof BoundedIntTRSProblem;
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        final FreshNameGenerator generator = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        assert obl instanceof BoundedIntTRSProblem : "Wrong obligation type!";
        final BoundedIntTRSProblem boundedIntTRS = ((BoundedIntTRSProblem) obl).renameVariables(generator);
        final ImmutableSet<IGeneralizedRule> rules = boundedIntTRS.getRules();

        final LinkedHashSet<IGeneralizedRule> resultRules = new LinkedHashSet<>();

        for (final IGeneralizedRule rule : rules) {
            final Map<TRSVariable, IntegerType> rangeInfo =
                boundedIntTRS.getBoundInformation().getBoundInformationMap().get(rule);

            final CastSymbolRemover crs = new CastSymbolRemover(rule, rangeInfo);
            final BoundedRuleTransformer brt =
                new BoundedRuleTransformer(crs.getOutput(), rangeInfo, this.arguments, generator, aborter);
            resultRules.addAll(brt.getOutput());
        }
        final IRSProblem resultIntTRS = new IRSProblem(ImmutableCreator.create(resultRules));

        return ResultFactory.proved(resultIntTRS, YNMImplication.SOUND, new BoundedIntTRSToIntTRSProof());
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me)
     */
    class BoundedIntTRSToIntTRSProof extends DefaultProof {
        /** Create the proof. */
        public BoundedIntTRSToIntTRSProof() {
            super();
            this.shortName = "BoundedIntTRSToIntTRS";
            this.longName = "BoundedIntTRSToIntTRSProcessor";
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            return "Removed the cast-operations, but maintained the semantics!";
        }
    }
}
