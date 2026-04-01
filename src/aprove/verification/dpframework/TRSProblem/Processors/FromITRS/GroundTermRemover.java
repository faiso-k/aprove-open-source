package aprove.verification.dpframework.TRSProblem.Processors.FromITRS;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor removes ground terms that appear inside every occurrence of
 * some function application without being changed.
 *
 * <pre>
 * f(x, y, 0, NIL) -&gt; ...
 * ... -&gt; f(x, y, z, NIL)
 * ... -&gt; f(x, y, 0, NIL)
 * results in
 * f(x, y, 0) -&gt; ...
 * ... -&gt; f(x, y, z)
 * ... -&gt; f(x, y, 0)
 * </pre>
 * @author cotto
 */
public class GroundTermRemover extends QTRSProcessor {
    /**
     * The proof for this processor giving information about the ground terms
     * and how they are removed.
     * @author cotto
     */
    private class GroundTermsRemoverProof extends ArgumentsRemovalProof {
        /**
         * The ground terms that were removed.
         */
        private final Collection<TRSTerm> groundTerms;

        /**
         * Create a new proof.
         * @param removedArgs information about removed arguments.
         * @param names information about name changes.
         * @param groundTermsParam the ground terms that were removed
         */
        public GroundTermsRemoverProof(
                final CollectionMap<FunctionSymbol, Integer> removedArgs,
                final Map<FunctionSymbol, FunctionSymbol> names,
                final Collection<TRSTerm> groundTermsParam) {
            super(removedArgs, names);
            this.groundTerms = groundTermsParam;
        }

        /**
         * @return the proof as a nice string representation.
         * @param eu an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb =
                new StringBuilder(
                    "Some arguments are removed because they always contain the same ground term.");
            sb.append(eu.linebreak());
            sb.append("We removed the following ground terms:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.groundTerms, 3));
            sb.append(eu.linebreak());
            super.export(eu, sb);
            return sb.toString();
        }
    }

    /**
     * Gather all function symbols and mark all relevant positions as
     * duplicates.
     * @param qtrs the qtrs
     * @param functionApplications this collection will be filled with all
     * function applications
     * @param syms an empty set, will be filled with all function symbols
     * @param groundTerms information about arguments always holding the same
     * ground term
     * @param the defined symbols will be added here
     */
    private void init(final QTRSProblem qtrs,
        final Collection<TRSFunctionApplication> functionApplications,
        final Collection<FunctionSymbol> syms,
        final Map<FunctionSymbol, Map<Integer, TRSTerm>> groundTerms,
        final Collection<FunctionSymbol> definedSymbols) {
        // Now, find all applications
        final Stack<TRSTerm> terms = new Stack<TRSTerm>();
        terms.addAll(qtrs.getTerms());
        while (!terms.isEmpty()) {
            final TRSTerm term = terms.pop();
            if (term.isVariable()) {
                continue;
            }
            final TRSFunctionApplication fa = (TRSFunctionApplication) term;
            terms.addAll(fa.getSubTerms());
            terms.remove(fa);
            syms.add(fa.getRootSymbol());
            functionApplications.add(fa);
        }

        // Find out which symbols are defined
        for (final Rule rule : qtrs.getR()) {
            definedSymbols.add(rule.getRootSymbol());
        }

        /*
         * For every function symbol and every argument position mark the
         * corresponding positions to the left.
         */
        for (final FunctionSymbol fs : syms) {
            final int arity = fs.getArity();
            if (arity == 0) {
                continue;
            }
            final Map<Integer, TRSTerm> groundColl =
                new LinkedHashMap<Integer, TRSTerm>();

            final CollectionMap<Integer, Integer> coll =
                new CollectionMap<Integer, Integer>();
            for (int i = 0; i < arity; i++) {
                final Integer iInt = Integer.valueOf(i);
                groundColl.put(iInt, null);
                final Collection<Integer> preds = new LinkedHashSet<Integer>(i);
                for (int j = 0; j < i; j++) {
                    preds.add(Integer.valueOf(j));
                }
                coll.put(iInt, preds);
            }
            groundTerms.put(fs, groundColl);
        }
    }

    /**
     * Yes, we can.
     * @param qtrs any qtrs
     * @return true
     */
    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return true;
    }

    /**
     * Start working on the given QTRS.
     * @param qtrs some qtrs
     * @param aborter an aborter
     * @return the QTRS with useless ground terms removed (together with a proof
     * and such)
     * @param rti don't know
     * @throws AbortionException never.
     */
    @Override
    protected Result processQTRS(final QTRSProblem qtrs,
        final Abortion aborter,
        final RuntimeInformation rti)
            throws AbortionException {
        final Collection<FunctionSymbol> syms =
            new LinkedHashSet<FunctionSymbol>();
        final Collection<TRSFunctionApplication> functionApplications =
            new LinkedHashSet<TRSFunctionApplication>();
        /*
         * For every function symbol and position find out if there is a
         * ground term that always is present at that position.
         */
        final Map<FunctionSymbol, Map<Integer, TRSTerm>> groundTerms =
            new LinkedHashMap<FunctionSymbol, Map<Integer, TRSTerm>>();

        final Collection<FunctionSymbol> definedSymbols =
            new LinkedHashSet<FunctionSymbol>();

        /*
         * Get all function symbols and their applications, furthermore
         * initialize the ground term information.
         */
        this.init(qtrs, functionApplications, syms, groundTerms, definedSymbols);

        /*
         * Now, for every function application and position inside check if at
         * that position the same constant term appears that was already seen.
         */
        for (final TRSFunctionApplication fa : functionApplications) {
            final FunctionSymbol rootFS = fa.getRootSymbol();
            final int arity = rootFS.getArity();
            if (arity == 0) {
                continue;
            }
            final Map<Integer, TRSTerm> groundColl = groundTerms.get(rootFS);
            assert (groundColl != null) : "No map for symbol '" + rootFS
                + "', function applications: " + functionApplications;
            /*
             * Now, for the current function application, check if the term
             * seen here is identical to the term we already know for that
             * position.
             */
            final Collection<Integer> remove = new LinkedList<Integer>();
            for (final Map.Entry<Integer, TRSTerm> entry : groundColl.entrySet()) {
                final Integer pos = entry.getKey();
                final TRSTerm termAtPos = fa.getArgument(pos.intValue());
                if (termAtPos instanceof TRSFunctionApplication) {
                    final FunctionSymbol fs =
                        ((TRSFunctionApplication) termAtPos).getRootSymbol();
                    if (definedSymbols.contains(fs)) {
                        remove.add(pos);
                        continue;
                    }
                }
                if (!termAtPos.isGroundTerm()) {
                    remove.add(pos);
                    continue;
                }
                final TRSTerm knownTerm = groundColl.get(pos);
                if (knownTerm == null) {
                    // first time we see this position
                    groundColl.put(pos, termAtPos);
                } else if (!knownTerm.equals(termAtPos)) {
                    // different ground terms :(
                    remove.add(pos);
                }
            }
            for (final Integer rem : remove) {
                groundColl.remove(rem);
            }
        }

        // For every function symbol mark the positions that can be deleted
        boolean didSomething = false;
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved =
            new CollectionMap<FunctionSymbol, Integer>();
        for (final FunctionSymbol sym : syms) {
            if (sym.getArity() == 0) {
                continue;
            }

            // what about the ground terms?
            final Map<Integer, TRSTerm> groundColl = groundTerms.get(sym);

            if (!groundColl.isEmpty()) {
                didSomething = true;
                positionsToBeRemoved.add(sym, groundColl.keySet());
            }
        }

        if (!didSomething) {
            // No argument can be removed
            return ResultFactory.unsuccessful();
        }

        // collect the ground terms that will be removed
        final Collection<TRSTerm> removedGroundTerms = new LinkedHashSet<TRSTerm>();
        for (final TRSFunctionApplication fa : functionApplications) {
            final Collection<Integer> removedPositions =
                positionsToBeRemoved.get(fa.getRootSymbol());
            if (removedPositions != null) {
                for (final Integer integer : removedPositions) {
                    removedGroundTerms.add(fa.getArgument(integer.intValue()));
                }
            }
        }

        // Construct the result
        final Pair<QTRSProblem, Map<FunctionSymbol, FunctionSymbol>> pair =
            HelperClass.getResultingQTRS(qtrs, positionsToBeRemoved);

        final GroundTermsRemoverProof proof =
            new GroundTermsRemoverProof(positionsToBeRemoved, pair.y,
                removedGroundTerms);
        return ResultFactory.proved(pair.x, YNMImplication.EQUIVALENT, proof);
    }

}
