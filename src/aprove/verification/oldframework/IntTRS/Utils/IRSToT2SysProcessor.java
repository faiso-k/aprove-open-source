package aprove.verification.oldframework.IntTRS.Utils;

import java.util.*;

import aprove.input.Programs.t2.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Transforms IRS (without terms) to an integer transition system as used by T2.
 * @author Marc Brockschmidt
 */
public class IRSToT2SysProcessor extends Processor.ProcessorSkeleton {

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    @Override
    public Result process(
        final BasicObligation obligation,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert (obligation instanceof IRSwTProblem);
        final IRSProblem problem = obligation instanceof IRSProblem ? (IRSProblem) obligation : new IRSProblem((IRSwTProblem) obligation);
        final Pair<T2IntSys, Map<FunctionSymbol, Integer>> pair = T2ExportTool.transformIntTRSToT2(problem);
        final T2IntSys res = pair.x;
        final Map<FunctionSymbol, Integer> pcMap = pair.y;
        res.setParent(obligation);

        return ResultFactory.proved(res, YNMImplication.EQUIVALENT, new IRSToT2SysProof(pcMap));
    }

    /**
     * Modelling IntTRS to T2 proof result
     *
     * The finest proof.
     * @author Marc Brockschmidt
     */
    public class IRSToT2SysProof extends DefaultProof {

        /** Map from function symbols to location IDs */
        private final Map<FunctionSymbol, Integer> pcMap;

        /** Create the proof. */
        public IRSToT2SysProof(final Map<FunctionSymbol, Integer> map) {
            this.shortName = "IRS2T2";
            this.longName = "IRS to T2 Integer Transition System Processor";
            this.pcMap = map;
        }

        /**
         * @param eu export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder builder = new StringBuilder();
            builder.append("Transformed input IRS into an integer transition system."
                + "Used the following mapping from defined symbols to location IDs:");
            builder.append(eu.linebreak());

            final List<Pair<String, String>> l = new LinkedList<>();
            for (final Map.Entry<FunctionSymbol, Integer> e : this.pcMap.entrySet()) {
                l.add(new Pair<>(e.getKey().toString(), e.getValue().toString()));
            }
            builder.append(eu.set(l, Export_Util.RULES));
            return builder.toString();
        }
    }
}
