package aprove.verification.diophantine;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.Util.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A dirty little hack to fetch SearchAlgorithms, so aprove-internal solvers can be used "directly".
 *
 * It's a hack, but it works, and that's what counts ;)
 *
 * @author bearperson
 * @version $Id$
 */
public class EngineHack {

    static private final Map<String, DiophantineProcessor> processorCache =
        Collections.synchronizedMap(new HashMap<String, DiophantineProcessor>());


    public static SearchAlgorithm getSearchAlg(final DiophantineProcessor pseudoProc,
        final DefaultValueMap<String, BigInteger> allRanges) {
        return EngineHack.getSearchAlg(pseudoProc, allRanges, true);
    }

    public static SearchAlgorithm getSearchAlg(final DiophantineProcessor pseudoProc,
        final DefaultValueMap<String, BigInteger> allRanges,
        final boolean simplify) {
        final Engine engine = pseudoProc.getEngine();
        final DiophantineSATConverter dioSatConverter = pseudoProc.getSatConverter();

        SearchAlgorithm searchAlg;
        //final DefaultValueMap<String, BigInteger> allRanges = new DefaultValueMap<String, BigInteger>(range);

        // first take the search algorithm from the engine
        if (engine instanceof SatEngine) {
            // satEngines require a DiophantineSATConverter to build a
            // corresponding SearchAlgorithm, so this workaround is
            // (currently) needed
            final SatEngine satEngine = (SatEngine) engine;
            searchAlg = satEngine.getSearchAlgorithm(allRanges, dioSatConverter);
        }
        else {
            searchAlg = engine.getSearchAlgorithm(allRanges);
        }

        if (simplify) {
            // now wrap the Engine's search algorithm into the simplifying search
            // and return the latter
            final SimplifyingSearch simplSearch =
                SimplifyingSearch.create(searchAlg, true,
                    pseudoProc.getStripExponents(),
                    pseudoProc.getSimplification());

            return simplSearch;
        }
        return searchAlg;
    }

    public static SearchAlgorithm getSearchAlg(final String strategyArg,
        final DefaultValueMap<String, BigInteger> allRanges) {
        return EngineHack.getSearchAlg(strategyArg, allRanges, true);
    }

    public static SearchAlgorithm getSearchAlg(final String strategyArg,
        final DefaultValueMap<String, BigInteger> allRanges,
        final boolean simplify) {
        // As processors are stateless, we can cache a processor for a given strategy.
        DiophantineProcessor pseudoProc;
        pseudoProc = EngineHack.processorCache.get(strategyArg);
        if (pseudoProc == null) {
            // Create a processor with the given strategy options
            final ParamValue value = StrategyTranslator.value("Diophantine" + strategyArg);
            try {
                pseudoProc = (DiophantineProcessor) value.get(StrategyTranslator.standardProgram());
            } catch (final WrappedParamMgrException e) {
                throw new RuntimeException(e);
            }

            EngineHack.processorCache.put(strategyArg, pseudoProc);
        }

        // We still need to create a new SearchAlgorithm every time though, those do have state.
        return EngineHack.getSearchAlg(pseudoProc, allRanges, simplify);
    }

}
