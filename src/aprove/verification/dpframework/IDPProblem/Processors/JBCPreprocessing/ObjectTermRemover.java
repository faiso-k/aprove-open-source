package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor removes object term encodings.
 *
 * @author Marc Brockschmidt
 */
public class ObjectTermRemover extends ITRSProcessor {

    /**
     * The proof for this processor giving information about the ground terms
     * and how they are removed.
     * @author cotto
     */
    private class ObjectTermRemoverProof extends ArgumentsRemovalProof {
        /**
         * Create a new proof.
         * @param removedArgs information about removed arguments.
         * @param names information about name changes.
         */
        public ObjectTermRemoverProof(
                final ITRSProblem itrsProblem,
                final Collection<Rule> removedArgs) {
            super(itrsProblem, removedArgs);
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
                "Some arguments are removed because they encode objects.");
            sb.append(eu.linebreak());
            /*sb.append("We removed the following ground terms:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.groundTerms, 3));
            sb.append(eu.linebreak());*/
            super.export(eu, sb);
            return sb.toString();
        }
    }

    /**
     * Yes, we can.
     * @param itrs any itrs
     * @return true
     */
    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }

    Collection<TRSFunctionApplication> getFunctionApplications(final Set<GeneralizedRule> rules) {
        final Collection<TRSFunctionApplication> functionApplications =
            new LinkedHashSet<TRSFunctionApplication>();
        for (final GeneralizedRule rule : rules) {
            for (final TRSTerm t : rule.getTerms()) {
                if (t instanceof TRSFunctionApplication) {
                    for (final TRSFunctionApplication s : t.getNonVariableSubTerms()) {
                        functionApplications.add(s);
                    }
                }
            }
        }
        return functionApplications;
    }

    public Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                  Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                  Collection<Rule>> processRulePair(
            final Set<GeneralizedRule> pRules,
            final Set<GeneralizedRule> rRules,
            final IDPPredefinedMap predefinedMap) {
        // Compute function applications occuring in the TRS:
        final Collection<TRSFunctionApplication> funcApps = new LinkedHashSet<TRSFunctionApplication>();
        funcApps.addAll(this.getFunctionApplications(pRules));
        funcApps.addAll(this.getFunctionApplications(rRules));

        /*
         * Now, for every function application and position inside check if at
         * that position an object appears. If yes, mark it to remove it later.
         */
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved =
            new CollectionMap<FunctionSymbol, Integer>();
        boolean didSomething = false;
        for (final TRSFunctionApplication fa : funcApps) {
            final FunctionSymbol rootFS = fa.getRootSymbol();
            final int arity = rootFS.getArity();

            for (int i = 0; i < arity; i++) {
                if (fa.getArgument(i).getName().startsWith("java.lang.Object")) {
                    //Special-case arrays:
                    if ((((TRSFunctionApplication) fa.getArgument(i)).getRootSymbol().getArity() < 1)
                            || !((TRSFunctionApplication) fa.getArgument(i)).getArgument(0).getName().startsWith("ARRAY")) {
                        positionsToBeRemoved.add(rootFS, i);
                        didSomething = true;
                    }
                }
            }
        }

        if (!didSomething) {
            // No argument can be removed
            return null;
        }

        // Construct the result
        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRPair =
            HelperClass.getResultingRules(rRules, predefinedMap, positionsToBeRemoved, new LinkedHashSet<FunctionSymbol>());

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newPPair =
            HelperClass.getResultingRules(pRules, predefinedMap, positionsToBeRemoved, new LinkedHashSet<FunctionSymbol>());

        return new Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                          Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                          Collection<Rule>>(newPPair, newRPair,  ArgumentsRemovalProof.getFilterRules(positionsToBeRemoved, newPPair.y));
    }

    /**
     * Start working on the given ITRS.
     * @param itrs some itrs
     * @param aborter an aborter
     * @return the ITRS with object arguments removed (together with a proof
     * and such)
     * @throws AbortionException never.
     */
    @Override
    protected Result processITRSProblem(final ITRSProblem itrs, final Abortion aborter)
    throws AbortionException {
        final Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                     Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                     Collection<Rule>>
             resultTriple =
                 this.processRulePair(Collections.EMPTY_SET, itrs.getR(), itrs.getPredefinedMap());

        if (resultTriple == null) {
            // No argument can be removed
            return ResultFactory.unsuccessful();
        }

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRulesPair = resultTriple.y;
        final Set<GeneralizedRule> newRules = newRulesPair.x;
        final Collection<Rule> positionsToBeRemoved = resultTriple.z;


        final IQTermSet newQ = new IQTermSet(HelperClass.getNewQ(newRules), itrs.getPredefinedMap());
        final ITRSProblem newItrs = ITRSProblem.create(newRules, newQ);

        final ObjectTermRemoverProof proof =
            new ObjectTermRemoverProof(itrs, positionsToBeRemoved);
        return ResultFactory.proved(newItrs, YNMImplication.EQUIVALENT, proof);
    }

}
