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
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor removes arguments which are free in some rule in the
 * TRS.
 *
 * @author Marc Brockschmidt
 */
public class FreeVariableTermRemover extends ITRSProcessor {

    /**
     * The proof for this processor giving information about the ground terms
     * and how they are removed.
     * @author cotto
     */
    private class FreeVariableTermRemoverProof extends ArgumentsRemovalProof {
        /**
         * Create a new proof.
         * @param removedArgs information about removed arguments.
         */
        public FreeVariableTermRemoverProof(
                final ITRSProblem itrsProblem,
                final Collection<Rule> removedArgs) {
            super(itrsProblem, removedArgs);
            //this.groundTerms = groundTermsParam;
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

    public static CollectionMap<FunctionSymbol, Integer> getPositionFilter(
            final Set<GeneralizedRule> pRules,
            final Set<GeneralizedRule> rRules,
            final IDPPredefinedMap predefinedMap,
            final boolean alsoFilterOnR,
            final boolean haveToFilter,
            final int maxNumberOfBoundVarsToFilterAway) {
        //Only consider free variables in P as important:
        /*
         * For each rule in P, identify the positions of subterms which contain
         * a free variable. Mark these positions for removal.
         */
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved =
            new CollectionMap<FunctionSymbol, Integer>();

        final Collection<GeneralizedRule> allRules = new LinkedHashSet<GeneralizedRule>();
        allRules.addAll(pRules);
        if (alsoFilterOnR) {
            allRules.addAll(rRules);
        }

        /*
         * The ARRAY symbol is special: We only filter the first argument
         * if it is _always_ a free var.
         */
        boolean arrayHasBoundVarOnFirstPos = false;

        final Collection<FunctionSymbol> usedInP =
            new LinkedHashSet<FunctionSymbol>();

        final Collection<FunctionSymbol> definedSymbolInP =
            new LinkedHashSet<FunctionSymbol>();
        for (final GeneralizedRule rule : pRules) {
            definedSymbolInP.add(rule.getLeft().getRootSymbol());
        }

        boolean didSomething = false;
        boolean changed = false;
        do {
            arrayHasBoundVarOnFirstPos = false;
            changed = false;
            for (final GeneralizedRule rule : allRules) {
                final Collection<TRSVariable> boundVars =
                    new LinkedHashSet<TRSVariable>();
                final Stack<TRSTerm> lSubterms = new Stack<TRSTerm>();
                lSubterms.add(rule.getLeft());
                while (!lSubterms.isEmpty()) {
                    final TRSTerm t = lSubterms.pop();
                    if (t instanceof TRSVariable) {
                        boundVars.add((TRSVariable) t);
                    } else if (t instanceof TRSFunctionApplication) {
                        //Check all positions which are not yet filtered:
                        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                        final FunctionSymbol fs = fa.getRootSymbol();
                        usedInP.add(fs);
                        for (int i = 0; i < fs.getArity(); i++) {
                            if (!positionsToBeRemoved.contains(fs, i) || (fs.getName().equals(ArrayTransformer.ARRAY_CONSTR.getName()) && i == 0)) {
                                lSubterms.add(fa.getArgument(i));
                            }
                        }
                    }
                }

                if (!(rule.getRight() instanceof TRSFunctionApplication)) {
                    continue;
                }
                //Now identify all subterms on the rhs which use unbound vars:
                final Stack<Pair<TRSFunctionApplication, Position>> rSubterms = new Stack<Pair<TRSFunctionApplication, Position>>();
                rSubterms.add(
                        new Pair<TRSFunctionApplication, Position>(
                                (TRSFunctionApplication) rule.getRight(),
                                Position.create()));

                while (!rSubterms.isEmpty()) {
                    final Pair<TRSFunctionApplication, Position> p = rSubterms.pop();
                    final TRSFunctionApplication fa = p.x;
                    final Position pos = p.y;
                    final FunctionSymbol fs = fa.getRootSymbol();
                    for (int i = 0; i < fs.getArity(); i++) {
                        if (!positionsToBeRemoved.contains(fs, i) || (fs.getName().equals(ArrayTransformer.ARRAY_CONSTR.getName()) && i == 0)) {
                            final TRSTerm arg =  fa.getArgument(i);
                            if (arg instanceof TRSVariable) {
                                if (!boundVars.contains(arg)) {
                                    assert (!predefinedMap.isPredefined(fs));
                                    //If this is not defined, try higher up:
                                    boolean foundFilterPos = false;
                                    if (!definedSymbolInP.contains(fs) && !pos.isEmptyPosition()) {
                                        int lastRemoved = i;
                                        Position curPos = pos;
                                        do {
                                            lastRemoved = curPos.lastIndex();
                                            curPos = curPos.shorten(1);
                                            final TRSFunctionApplication curSubterm = (TRSFunctionApplication) rule.getRight().getSubterm(curPos);
                                            final FunctionSymbol usedFs = curSubterm.getRootSymbol();
                                            final Set<TRSVariable> curSubtermVars = curSubterm.getVariables();
                                            int countBoundVars = 0;
                                            for (final TRSVariable v : curSubtermVars) {
                                                if (boundVars.contains(v)) {
                                                    countBoundVars++;
                                                }
                                            }

                                            if (countBoundVars >= maxNumberOfBoundVarsToFilterAway) {
                                                break;
                                            }

                                            if (definedSymbolInP.contains(usedFs) || (haveToFilter && curPos.isEmptyPosition())) {
                                                changed |= positionsToBeRemoved.add(usedFs, lastRemoved);
                                                didSomething = true;
                                                foundFilterPos = true;
                                                break;
                                            }
                                        } while (!curPos.isEmptyPosition());
                                    }

                                    if (haveToFilter && !foundFilterPos) {
                                        changed |= positionsToBeRemoved.add(fs, i);
                                        didSomething = true;
                                    }
                                } else {
                                    if (fs.getName().equals(ArrayTransformer.ARRAY_CONSTR.getName()) && i == 0) {
                                        arrayHasBoundVarOnFirstPos = true;
                                    }
                                }
                            } else {
                                final TRSFunctionApplication argFa = (TRSFunctionApplication) arg;
                                final FunctionSymbol argFs = argFa.getRootSymbol();
                                if (!predefinedMap.isPredefined(argFs) && !argFs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)) {
                                    rSubterms.add(
                                            new Pair<TRSFunctionApplication, Position>(argFa, pos.append(i)));
                                }
                            }
                        }
                    }
                }
            }
        } while (changed);


        if (!alsoFilterOnR) {
            changed = false;
            do {
                arrayHasBoundVarOnFirstPos = false;
                changed = false;
                for (final GeneralizedRule rule : rRules) {
                    final Collection<TRSVariable> boundVars =
                        new LinkedHashSet<TRSVariable>();
                    final Stack<TRSTerm> lSubterms = new Stack<TRSTerm>();
                    lSubterms.add(rule.getLeft());
                    while (!lSubterms.isEmpty()) {
                        final TRSTerm t = lSubterms.pop();
                        if (t instanceof TRSVariable) {
                            boundVars.add((TRSVariable) t);
                        } else if (t instanceof TRSFunctionApplication) {
                            //Check all positions which are not yet filtered:
                            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                            final FunctionSymbol fs = fa.getRootSymbol();
                            for (int i = 0; i < fs.getArity(); i++) {
                                if (!positionsToBeRemoved.contains(fs, i) || (fs.getName().equals(ArrayTransformer.ARRAY_CONSTR.getName()) && i == 0)) {
                                    lSubterms.add(fa.getArgument(i));
                                }
                            }
                        }
                    }

                    //Now identify all subterms on the rhs which use unbound vars:
                    final Stack<Pair<TRSFunctionApplication, Position>> rSubterms = new Stack<Pair<TRSFunctionApplication, Position>>();
                    rSubterms.add(
                            new Pair<TRSFunctionApplication, Position>(
                                    (TRSFunctionApplication) rule.getRight(),
                                    Position.create()));

                    while (!rSubterms.isEmpty()) {
                        final Pair<TRSFunctionApplication, Position> p = rSubterms.pop();
                        final TRSFunctionApplication fa = p.x;
                        final Position pos = p.y;
                        final FunctionSymbol fs = fa.getRootSymbol();
                        for (int i = 0; i < fs.getArity(); i++) {
                            if (!positionsToBeRemoved.contains(fs, i) || (fs.getName().equals(ArrayTransformer.ARRAY_CONSTR.getName()) && i == 0)) {
                                final TRSTerm arg =  fa.getArgument(i);
                                if (arg instanceof TRSVariable) {
                                    if (!boundVars.contains(arg)) {
                                        assert (!predefinedMap.isPredefined(fs));
                                        //If this was used in P, try to filter higher up:
                                        if (usedInP.contains(fs) && !pos.isEmptyPosition()) {
                                            int lastRemoved = i;
                                            Position curPos = pos;
                                            do {
                                                lastRemoved = curPos.lastIndex();
                                                curPos = curPos.shorten(1);
                                                final FunctionSymbol usedFs = ((TRSFunctionApplication) rule.getRight().getSubterm(curPos)).getRootSymbol();
                                                if (!usedInP.contains(usedFs)) {
                                                    changed |= positionsToBeRemoved.add(usedFs, lastRemoved);
                                                    didSomething = true;
                                                }
                                            } while (!curPos.isEmptyPosition());
                                        } else {
                                            changed |= positionsToBeRemoved.add(fs, i);
                                            didSomething = true;
                                        }
                                    } else {
                                        if (fs.getName().equals(ArrayTransformer.ARRAY_CONSTR.getName()) && i == 0) {
                                            arrayHasBoundVarOnFirstPos = true;
                                        }
                                    }
                                } else {
                                    final TRSFunctionApplication argFa = (TRSFunctionApplication) arg;
                                    final FunctionSymbol argFs = argFa.getRootSymbol();
                                    if (!predefinedMap.isPredefined(argFs) && !argFs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)) {
                                        rSubterms.add(
                                                new Pair<TRSFunctionApplication, Position>(argFa, pos.append(i)));
                                    }
                                }
                            }
                        }
                    }
                }
            } while (changed);
        }

        //Array length was bound at some point. Don't remove it:
        if (arrayHasBoundVarOnFirstPos) {
            //positionsToBeRemoved.remove(ArrayTransformer.ARRAY_CONSTR, 0);
        }

        if (!didSomething) {
            // No argument can be removed
            return null;
        }

        return positionsToBeRemoved;
    }

    public static Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                  Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                  Collection<Rule>> processRulePair(
                          final Set<GeneralizedRule> pRules,
                          final Set<GeneralizedRule> rRules,
                          final IDPPredefinedMap predefinedMap,
                          final boolean alsoFilterOnR,
                          final boolean haveToFilter,
                          final int maxNumberOfBoundVarsToFilterAway) {
        final CollectionMap<FunctionSymbol, Integer> positionsToBeRemoved =
                FreeVariableTermRemover.getPositionFilter(pRules, rRules, predefinedMap, alsoFilterOnR, haveToFilter, maxNumberOfBoundVarsToFilterAway);

        if (positionsToBeRemoved == null) {
            return null;
        }

        // Construct the result
        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRPair =
            HelperClass.getResultingRules(rRules, predefinedMap, positionsToBeRemoved, new LinkedHashSet<FunctionSymbol>());

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newPPair =
            HelperClass.getResultingRules(pRules, predefinedMap, positionsToBeRemoved, new LinkedHashSet<FunctionSymbol>());

        /*
         * Now replace all predefined symbols with a free variable by free
         * variable:
         */
        newPPair.x = FreeVariableTermRemover.filterConditions(newPPair.x, predefinedMap);
        newRPair.x = FreeVariableTermRemover.filterConditions(newRPair.x, predefinedMap);

        return new Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                          Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                          Collection<Rule>>(newPPair, newRPair, ArgumentsRemovalProof.getFilterRules(positionsToBeRemoved, newPPair.y));
    }

    public static Set<GeneralizedRule> filterConditions(final Collection<GeneralizedRule> rules, final IDPPredefinedMap predefinedMap) {
        final Set<GeneralizedRule> newRules = new LinkedHashSet<GeneralizedRule>();
        for (final GeneralizedRule rule : rules) {
            final Collection<TRSVariable> boundVars = rule.getLeft().getVariables();
            TRSTerm newRight = rule.getRight();

            //Find all occurrences of predefined symbols which have a free
            //variable as argument, replac'em:
            boolean changedRight = true;
            while (changedRight) {
                changedRight = false;
                subtermSearch: for (final Position pos : newRight.getPositions()) {
                    final TRSTerm subterm = newRight.getSubterm(pos);
                    if (subterm instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication fa = (TRSFunctionApplication) subterm;
                        final FunctionSymbol fs = fa.getRootSymbol();
                        if (predefinedMap.isPredefined(fs)) {
                            for (int argNum = 0; argNum < fs.getArity(); argNum++) {
                                final TRSTerm arg = fa.getArgument(argNum);
                                if (arg instanceof TRSVariable && !boundVars.contains(arg)) {
                                    final TRSTerm newTerm;
                                    //For and, we know this part can always be satisfied, so project on the other:
                                    if (predefinedMap.isLand(fs)) {
                                        if (argNum == 0) {
                                            newTerm = fa.getArgument(1);
                                        } else {
                                            newTerm = fa.getArgument(0);
                                        }
                                    /*
                                     * For all others, we know it may be true,
                                     * or not. Re-use the free variable,
                                     */
                                    } else {
                                        newTerm = TRSTerm.createVariable(arg.getName() + "_" + pos.toString());
                                    }
                                    newRight = newRight.replaceAt(pos, newTerm);
                                    changedRight = true;
                                    break subtermSearch;
                                }
                            }
                        }
                    }
                }
            }
            newRules.add(GeneralizedRule.create(rule.getLeft(), newRight));
        }
        return newRules;
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
                 FreeVariableTermRemover.processRulePair(Collections.EMPTY_SET, itrs.getR(), itrs.getPredefinedMap(), true, true, 0);

        if (resultTriple == null) {
            // No argument can be removed
            return ResultFactory.unsuccessful();
        }

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRulesPair = resultTriple.y;
        final Set<GeneralizedRule> newRules = newRulesPair.x;
        final Collection<Rule> positionsToBeRemoved = resultTriple.z;


        final IQTermSet newQ = new IQTermSet(HelperClass.getNewQ(newRules), itrs.getPredefinedMap());
        final ITRSProblem newItrs = ITRSProblem.create(newRules, newQ);

        final FreeVariableTermRemoverProof proof =
            new FreeVariableTermRemoverProof(itrs, positionsToBeRemoved);
        return ResultFactory.proved(newItrs, YNMImplication.EQUIVALENT, proof);
    }

}
