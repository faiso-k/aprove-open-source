package aprove.verification.idpframework.Processors.Filters;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Algorithms.Unification.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class FreeVariablesFilter extends AbstractIDPFilter<Result, TIDPProblem> {

    public enum FreeVariablesHandlingMode {
        RECKLESS,
        SAFE
    }

    private class FunctionArityMap extends LinkedHashMap<IFunctionSymbol<?>, List<Boolean>> {
        /**
         *
         */
        private static final long serialVersionUID = -747818621058879270L;

        @SuppressWarnings("unchecked")
        public FunctionArityMap(final IDPProblem idp, final Boolean defaultValue) {
            for (final IFunctionSymbol<?> fs : idp.getIdpGraph().getFunctionSymbols()) {
                if (!fs.isPredefined()) {
                    final LinkedList<Boolean> list = new LinkedList<Boolean>();
                    for (int i = 0; i < fs.getArity(); i++) {
                        list.add(defaultValue);
                    }
                    this.put(fs, list);
                }
            }
        }
    }

    public FreeVariablesFilter() {
        super("FreeVariablesFilter", FilterMode.REMOVE_FILTERED_ATOMS);
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(TIDPProblem idp, final Abortion aborter) throws AbortionException {
        TIDPProblem newIDP;
        FilterReplacement filter;

        FilterReplacement totalFilter = new FilterReplacement();

        boolean changed = false;
        boolean successfulRun;

        do {
            filter = this.createFilter(idp, aborter);

            totalFilter = totalFilter.appendFilter(filter);

            newIDP = this.createNewIDP(idp, filter, aborter);

            if (newIDP != idp) {
                changed = true;
                successfulRun = true;
            } else {
                successfulRun = false;
            }

            idp = newIDP;
        } while (successfulRun);


        //System.exit(1);

        if (!changed) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(newIDP, YNMImplication.EQUIVALENT, new FreeVariablesFilterProof(totalFilter));
        }
    }

    private FilterReplacement createFilter(final IDPProblem idp, final Abortion aborter) throws AbortionException {
        // konstante Fkt.: gilt als benutzte Position
        // linke Seite von Regeln: weich filtern
        // rechte Seite: hart filtern
        // FP-Iteration
        // f(x) -> f(h(x-y)): h nullstellig
        final FunctionArityMap retainedPositions = new FunctionArityMap(idp, false);
        final FunctionArityMap hardFilter        = new FunctionArityMap(idp, true);
        final IDependencyGraph graph = idp.getIdpGraph();
        final ImmutableSet<IFunctionSymbol<?>> definedSymbols = graph.getDefinedSymbols();

        for (final IEdge edge : idp.getIdpGraph().getEdges()) {
            final Itpf conditions = idp.getIdpGraph().getEdgeConditions().get(edge);

            for (final ItpfConjClause clause : conditions.getClauses()) {
                final Set<Pair<ITerm<?>, ITerm<?>>> unificationTerms = new LinkedHashSet<Pair<ITerm<?>,ITerm<?>>>();
                for (final Map.Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                    if (literal.getKey().isItp() && literal.getValue())  {
                        final ItpfItp itp = (ItpfItp) literal.getKey();

                        if (itp.getRelation() == ItpRelation.EQ) {
                            this.retainVarPositions(itp.getL(), retainedPositions);
                            this.retainVarPositions(itp.getR(), retainedPositions);

                            unificationTerms.add(new Pair<ITerm<?>, ITerm<?>>(itp.getL(), itp.getR()));
                        }
                    }
                }

                final Unification unification = new Unification(unificationTerms, graph.getPredefinedMap());
                final ISubstitution mgu = unification.getMgu();

                if (mgu != null) {
                    final PolyTermSubstitution polyTermMGU = TermToPolyTermSubstitution.create(mgu, graph.getPredefinedMap(), graph.getPolyInterpretation());
                    final ITerm<?> fromTerm = graph.getTerm(edge.from).applySubstitution(mgu);

                    ITerm<?> toTerm = graph.getTerm(edge.to);
                    // System.err.println("before apply: " + toTerm);
                    if (edge.from.equals(edge.to)) {
                        toTerm = toTerm.applySubstitution(graph.getLoopRenaming(edge.to));
                    }

                    toTerm = toTerm.applySubstitution(mgu);

                    final Set<IVariable<?>> sharedVars = fromTerm.getVariables();
                    sharedVars.retainAll(toTerm.getVariables());

                    final Set<IVariable<?>> leftVars = new LinkedHashSet<IVariable<?>>(sharedVars);
                    final Set<IVariable<?>> rightVars = new LinkedHashSet<IVariable<?>>(sharedVars);

                    final Set<IVariable<?>> fromVars = fromTerm.getVariables();
                    final Set<IVariable<?>> toVars = toTerm.getVariables();

                    for (final Map.Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                        if (literal.getKey().isItp() && literal.getValue()) {
                            final ItpfItp itp = ((ItpfItp) literal.getKey()).applySubstitution(polyTermMGU);

                            if (itp.getRelation().isRewriteRel()
                                    && fromVars.containsAll(itp.getL().getVariables())
                                    && toVars.containsAll(itp.getR().getVariables())) {

                                this.retainVarPositions(itp.getL(), retainedPositions);
                                this.retainVarPositions(itp.getR(), retainedPositions);

                                leftVars.addAll(itp.getL().getVariables());
                                rightVars.addAll(itp.getR().getVariables());
                            }
                        } else if (literal.getKey().isPoly() && literal.getValue()) {
                            final ItpfPolyAtom<?> polyAtom = ((ItpfPolyAtom<?>)literal.getKey());
                            final Polynomial<?> poly = polyAtom.getPoly();
                            final LinkedHashSet<IVariable<?>> polyLeftVars =
                                new LinkedHashSet<IVariable<?>>(poly.getVariables());
                            final LinkedHashSet<IVariable<?>> polyRightVars =
                                new LinkedHashSet<IVariable<?>>(polyLeftVars);

                            polyLeftVars.retainAll(fromVars);
                            polyRightVars.retainAll(toVars);

                            if (polyRightVars.isEmpty() ||
                                    IDP2toQDPProcessor.getPolyAtomCondition(polyAtom, polyLeftVars, polyRightVars, idp.getPredefinedMap()) != null) {
                                leftVars.addAll(polyLeftVars);

                                rightVars.addAll(polyRightVars);
                            }
                        }
                    }


                    // System.err.println("From: " + fromTerm);
                    this.processTerm(
                        fromTerm,
                        retainedPositions,
                        hardFilter,
                        leftVars,
                        definedSymbols,
                        false,
                        FreeVariablesHandlingMode.SAFE
                    );
                    // System.err.println("To: " + toTerm);
                    this.processTerm(
                        toTerm,
                        retainedPositions,
                        hardFilter,
                        rightVars,
                        definedSymbols,
                        false,
                        FreeVariablesHandlingMode.RECKLESS
                    );

                    if (Globals.DEBUG_MPLUECKER) {
                        System.err.println("HARD filter: " + hardFilter);
                    }
                }
            }
        }

        for (final java.util.Map.Entry<IFunctionSymbol<?>, List<Boolean>> e : retainedPositions.entrySet()) {
            final List<Boolean> hardFilterList = hardFilter.get(e.getKey());
            final List<Boolean> retained = retainedPositions.get(e.getKey());
            for (int i = 0; i < hardFilterList.size(); i++) {
                if (!hardFilterList.get(i).booleanValue()) {
                    //e.getValue().set(i, false);
                    retained.set(i, false);
                }
            }
        }

        final FunctionSymbolReplacement fsReplacement = this.createFsReplaceMap(idp, retainedPositions, aborter);

        return new FilterReplacement(fsReplacement, VarRenaming.EMPTY_RENAMING);
    }

    private boolean retainVarPositions(final ITerm<?> t,
        final FunctionArityMap retainedPositions) {
        if (t.isVariable()) {
            return true;
        } else {
            final IFunctionApplication<?> fa = (IFunctionApplication<?>) t;
            final IFunctionSymbol<?> rootSmybol = fa.getRootSymbol();
            final ImmutableArrayList<ITerm<?>> arguments = fa.getArguments();

            boolean retain = false;
            for (int i = arguments.size() - 1; i >= 0; i--) {
                final boolean retainedArg = this.retainVarPositions(arguments.get(i), retainedPositions);
                if (retainedArg && !rootSmybol.isPredefined()) {
                    retainedPositions.get(rootSmybol).set(i, true);
                    retain = true;
                }
            }

            return retain;
        }
    }

    private boolean processTerm(
            final ITerm<?> term,
            final FunctionArityMap softFilter,
            final FunctionArityMap hardFilter,
            final Collection<IVariable<?>> usedVariables,
            final ImmutableSet<IFunctionSymbol<?>> definedSymbols,
            final boolean isBelowDefinedSymbol, final FreeVariablesHandlingMode mode)
    {
        //System.err.println("Checking " + term);
        if (!term.isVariable()) {
            boolean retain = term.isConstant();
            final IFunctionApplication<?> fa = (IFunctionApplication<?>)term;
            final IFunctionSymbol<?> rootSymbol = fa.getRootSymbol();

            if (!retain) {
                retain = true;

                final boolean definedSymbol = definedSymbols.contains(rootSymbol);

                // System.err.println(fa);
                for (int i = 0; i < fa.getArguments().size(); i++) {
                    final ITerm<?> arg = fa.getArgument(i);
                    final boolean retainArg = this.processTerm(
                        arg,
                        softFilter,
                        hardFilter,
                        usedVariables,
                        definedSymbols,
                        definedSymbol || isBelowDefinedSymbol,
                        mode
                    );

                    if (!rootSymbol.isPredefined()) {
                       if (retainArg) {
                            softFilter.get(rootSymbol).set(i, true);
                        } else if (definedSymbol || !isBelowDefinedSymbol) {
                            if (mode == FreeVariablesHandlingMode.RECKLESS) {
                                // Variable muss hart gefiltert werden, sofort die Stelligkeit der Funktion verringern
                                //System.err.println("Hard filter: position " + position + ".");
                                hardFilter.get(rootSymbol).set(i, false);
                            } else {
                                retain = false;
                            }
                        } else {
                            retain = false;
                        }
                    } else if (!retainArg) {
                        retain = false;
                    }
                }
            }

            return retain;
        } else {
            return usedVariables.contains(term);
        }
    }

    @Override
    public boolean isCompatible(final Mark mark) {
        return false;
    }

    public static class FreeVariablesFilterProof extends AbstractFilterProof {

        public FreeVariablesFilterProof(final FilterReplacement filter) {
            super(filter);
        }

    }

}
