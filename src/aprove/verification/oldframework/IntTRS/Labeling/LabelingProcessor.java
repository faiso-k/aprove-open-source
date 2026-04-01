package aprove.verification.oldframework.IntTRS.Labeling;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This processor introduces new function symbols in order to distinguish
 * between cases.
 * @author Matthias Hoelzel, Marc Brockschmidt
 */
public class LabelingProcessor extends Processor.ProcessorSkeleton {
    /** Some argument class */
    public static class Arguments {
        /** */
        public int maxNumberOfCases = 2;
    }

    /** Some arguments */
    private final Arguments arguments;

    /**
     * Constructor.
     */
    public LabelingProcessor() {
        this.arguments = new Arguments();
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }
        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        final LabelingProof lp = new LabelingProof();

        Set<IGeneralizedRule> currentSystem = problem.getRules();
        Set<IGeneralizedRule> nextSystem = currentSystem;
        int iterations = 0;
        while (nextSystem != null) {
            currentSystem = nextSystem;
            final LabelingWorker lw = new LabelingWorker(currentSystem, this.arguments, ng, lp);
            nextSystem = lw.work();
            iterations++;
        }

        if (iterations == 1) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(
                new IRSProblem(ImmutableCreator.create(currentSystem)),
                YNMImplication.EQUIVALENT,
                lp);
        }
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me), Matthias Hoelzel (blame cotto instead)
     */
    class LabelingProof extends DefaultProof {
        /**
         * Some information about what we did here.
         */
        LinkedList<Pair<FunctionSymbol, Integer>> workingIndices;
        LinkedList<LinkedHashSet<TRSTerm>> valuesList;
        LinkedList<LinkedHashMap<TRSTerm, FunctionSymbol>> newSymbolsMaps;

        /**
         * Creates the proof.
         */
        public LabelingProof() {
            this.workingIndices = new LinkedList<>();
            this.valuesList = new LinkedList<>();
            this.newSymbolsMaps = new LinkedList<>();
        }

        /**
         * Fills in the information we need for a nice proof.
         * @param index
         * @param values
         * @param newSymbolsMap
         */
        public void fillInformation(
            final Pair<FunctionSymbol, Integer> index,
            final LinkedHashSet<TRSTerm> values,
            final LinkedHashMap<TRSTerm, FunctionSymbol> newSymbolsMap)
        {
            this.workingIndices.add(index);
            this.valuesList.add(values);
            this.newSymbolsMaps.add(newSymbolsMap);
        }

        /**
         * Generates a useless string.
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            final Iterator<Pair<FunctionSymbol, Integer>> indexIterator = this.workingIndices.iterator();
            final Iterator<LinkedHashSet<TRSTerm>> valuesIterator = this.valuesList.iterator();
            final Iterator<LinkedHashMap<TRSTerm, FunctionSymbol>> newSymbolMapsIterator = this.newSymbolsMaps.iterator();

            while (indexIterator.hasNext()) {
                this.export(eu, sb, indexIterator.next(), valuesIterator.next(), newSymbolMapsIterator.next());
            }

            return sb.toString();
        }

        /**
         * Helper method for the export.
         * @param eu some export helper
         * @param sb some string builder
         * @param index the current workin index
         * @param values the possible values
         * @param newSymbols the new symbols
         */
        private void export(
            final Export_Util eu,
            final StringBuilder sb,
            final Pair<FunctionSymbol, Integer> index,
            final LinkedHashSet<TRSTerm> values,
            final LinkedHashMap<TRSTerm, FunctionSymbol> newSymbols)
        {
            sb.append(index.x.export(eu));
            sb.append(eu.escape("_"));
            sb.append(index.y);
            sb.append(eu.tttext(" is "));
            boolean first = true;
            for (final TRSTerm t : values) {
                if (first) {
                    first = false;
                } else {
                    sb.append(eu.tttext(" or "));
                }
                sb.append(t.export(eu));
            }
            sb.append(eu.linebreak());
            sb.append(eu.tttext("Introducing the following new symbols: "));
            sb.append(eu.linebreak());
            for (final TRSTerm t : values) {
                sb.append(t.export(eu));
                sb.append(eu.rightarrow());
                sb.append(newSymbols.get(t).export(eu));
                sb.append(eu.linebreak());
            }
            sb.append(eu.linebreak());
        }
    }
}
