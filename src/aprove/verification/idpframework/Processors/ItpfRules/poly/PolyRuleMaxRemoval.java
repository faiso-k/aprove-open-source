package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.FreshVarGenerator;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.poly.PolyRuleMaxRemoval.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author MP
 */
/**
 * TODO: fix application mode count
 */
public class PolyRuleMaxRemoval<C extends SemiRing<C>> extends
        AbstractItpfReplaceRule.ItpfReplaceRuleSkeleton<MaxPolySubstitution<C>, Unused> {

    public PolyRuleMaxRemoval() {
        super(new ExportableString("[P] MaxRemoval"), new ExportableString(
            "[P] MaxRemoval"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null;
    }

    @Override
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isSound() {
        return true;
    }

    @Override
    public boolean isAtomicMark() {
        return true;
    }

    @Override
    public boolean isClauseMark() {
        return true;
    }

    @Override
    public boolean isContextFree() {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    public boolean isApplicable(final IDPProblem idp,
        final Itpf formula,
        final ApplicationMode mode) {
        return this.isApplicable(idp);
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
    }

    @Override
    protected ExecutionResult<Conjunction<Itpf>, Itpf> postProcess(final IDPProblem idp,
        final MaxPolySubstitution<C> context,
        final ItpfAndWrapper precondition,
        final ExecutionResult<Conjunction<Itpf>, Itpf> result,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {

        if (!context.getPreconditions().isEmpty()) {
            final List<Itpf> quantifiedResult =
                new ArrayList<Itpf>(result.result.size());

            for (final Itpf resultFormula : result.result) {
                final ItpfFactory itpfFactory = idp.getItpfFactory();
                Itpf completeFormula = resultFormula;

                for (final Itpf precon : context.getPreconditions()) {
                    completeFormula =
                        itpfFactory.create(itpfFactory.createImplication(
                            precon, completeFormula), true, ITerm.EMPTY_SET);
                }

                completeFormula =
                    itpfFactory.quantifyUniversal(context.getFreshVars(),
                        completeFormula);

                quantifiedResult.add(completeFormula);
            }

            return new ExecutionResult<Conjunction<Itpf>, Itpf>(
                new Conjunction<Itpf>(ImmutableCreator.create(quantifiedResult)),
                result.implication, result.usedApplications, result.fixpointReached);
        } else {
            return result;
        }
    }

    @Override
    protected MaxPolySubstitution<C> createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new MaxPolySubstitution<C>();
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final MaxPolySubstitution<C> context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {

        ItpfAtom newAtom = atom.applySubstitution(context);

        if (atom.isPoly()) {
            final PolyInterpretation<C> polyInterpretation =
                (PolyInterpretation<C>) idp.getIdpGraph().getPolyInterpretation();

            final ItpfPolyAtom<C> cleanedPoly =
                this.cleanPoly(polyInterpretation,
                    idp.getIdpGraph().getFreshVarGenerator(),
                    (ItpfPolyAtom<C>) atom, context, mode);

            newAtom = cleanedPoly;
        }

        if (atom != newAtom) {
            return this.getSingletonReturn(idp.getItpfFactory(), newAtom,
                positive, ImplicationType.EQUIVALENT, ApplicationMode.NoOp, false);
        } else {
            return null;
        }
    }

    private <C extends SemiRing<C>> PolyMaxVariable<C> getNextMaxSplitVar(final Polynomial<C> poly) {
        for (final Monomial<C> monomial : poly.getMonomials().keySet()) {
            for (final PolyVariable<C> variable : monomial.getExponents().keySet()) {
                if (variable.isMax()) {
                    final PolyMaxVariable<C> maxVariable =
                        (PolyMaxVariable<C>) variable;

                    for (final Polynomial<C> maxArgument : maxVariable.getArguments()) {
                        final PolyMaxVariable<C> deeperMax =
                            this.getNextMaxSplitVar(maxArgument);
                        if (deeperMax != null) {
                            return deeperMax;
                        }
                    }

                    return maxVariable;
                }
            }
        }
        return null;
    }

    private ItpfPolyAtom<C> cleanPoly(
        final PolyInterpretation<C> polyInterpretation,
        final FreshVarGenerator freshVarGenerator,
        ItpfPolyAtom<C> atom,
        final MaxPolySubstitution<C> maxPolySubstitution,
        ApplicationMode mode) {

        atom = atom.applySubstitution(maxPolySubstitution);

        PolyMaxVariable<C> nextMaxSplitVar = this.getNextMaxSplitVar(atom.getPoly());

        while (mode != ApplicationMode.NoOp && nextMaxSplitVar != null) {
            final String freshVarName =
                freshVarGenerator.getFreshVariableName("m", false);
            final SemiRingDomain<C> freshVarDomain =
                polyInterpretation.getRing().createUnknownVarRange();
            final IVariable<C> replacementVar =
                polyInterpretation.getFactory().createVariable(freshVarName,
                    freshVarDomain);
            final Polynomial<C> replacementVarPoly =
                polyInterpretation.getFactory().create(replacementVar);

            final Itpf splitPrecondition =
                this.createSplitPrecondition(polyInterpretation, nextMaxSplitVar,
                    replacementVarPoly);

            maxPolySubstitution.addSubstitution(nextMaxSplitVar,
                replacementVar, replacementVarPoly, splitPrecondition);

            atom = atom.applySubstitution(maxPolySubstitution);

            mode = mode.decreaseOneStep();
            if (mode != ApplicationMode.NoOp) {
                nextMaxSplitVar = this.getNextMaxSplitVar(atom.getPoly());
            }
        }

        return atom;
    }

    private Itpf createSplitPrecondition(final PolyInterpretation<C> polyInterpretation,
        final PolyMaxVariable<C> maxSplitVar,
        final Polynomial<C> replacementVarPoly) {
        final ItpfFactory itpfFactory =
            polyInterpretation.getConstraintFactory();
        final Set<ItpfConjClause> splitPreconditions =
            new LinkedHashSet<ItpfConjClause>();

        final Set<Polynomial<C>> encodedCases = new HashSet<Polynomial<C>>();

        for (final Polynomial<C> maxArgument : maxSplitVar.getArguments()) {
            final LiteralMap maxPrecondition = new LiteralMap();

            for (final Polynomial<C> leMaxArg : maxSplitVar.getArguments()) {
                if (maxArgument != leMaxArg) {
                    ConstraintType consraintType;
                    if (encodedCases.contains(leMaxArg)) {
                        consraintType = ConstraintType.GT;
                    } else {
                        consraintType = ConstraintType.GE;
                    }
                    maxPrecondition.put(itpfFactory.createPoly(
                        maxArgument.subtract(leMaxArg), consraintType,
                        polyInterpretation), true);
                }
            }

            maxPrecondition.put(itpfFactory.createPoly(
                maxArgument.subtract(replacementVarPoly), ConstraintType.EQ,
                polyInterpretation), true);

            splitPreconditions.add(itpfFactory.createClause(
                ImmutableCreator.create(maxPrecondition), ITerm.EMPTY_SET));

            encodedCases.add(maxArgument);
        }

        return itpfFactory.create(ImmutableCreator.create(splitPreconditions));
    }

    protected static class MaxPolySubstitution<R extends SemiRing<R>>
            extends IDPExportable.IDPExportableSkeleton implements PolyTermSubstitution, ReplaceContext {

        private final LinkedHashMap<PolyMaxVariable<R>, Polynomial<R>> map;
        private final List<IVariable<R>> freshVars;
        private final List<Itpf> preconditions;
        private final ReplaceContext replaceContext;

        public MaxPolySubstitution() {
            this.map = new LinkedHashMap<PolyMaxVariable<R>, Polynomial<R>>();
            this.freshVars = new ArrayList<IVariable<R>>();
            this.preconditions = new ArrayList<Itpf>();
            this.replaceContext = new ReplaceContext.ReplaceContextSkeleton();
        }

        public List<? extends IVariable<?>> getFreshVars() {
            return this.freshVars;
        }

        public List<Itpf> getPreconditions() {
            return this.preconditions;
        }

        public void addSubstitution(final PolyMaxVariable<R> maxVar,
            final IVariable<R> substitution,
            final Polynomial<R> replacementVarPoly,
            final Itpf splitPrecondition) {
            this.freshVars.add(substitution);
            this.preconditions.add(splitPrecondition);

            this.map.put(maxVar, replacementVarPoly);
        }

        @Override
        public boolean substitutesPoly(final PolyVariable<?> v) {
            return this.map.containsKey(v);
        }

        @Override
        public boolean substitutesPoly(final Collection<? extends PolyVariable<?>> vs) {
            for (final PolyVariable<?> v : vs) {
                if (this.substitutesPoly(v)) {
                    return true;
                }
            }
            return false;
        }

        @Override
        public <C extends SemiRing<C>> Polynomial<C> substitutePoly(final PolyVariable<C> v) {
            return (Polynomial<C>) this.map.get(v);
        }

        @Override
        public boolean isEmpty() {
            return this.map.isEmpty();
        }

        @Override
        public Set<? extends PolyVariable<?>> getPolyDomain() {
            return this.map.keySet();
        }

        @Override
        public boolean substitutesTerm(final IVariable<?> v) {
            return false;
        }

        @Override
        public <D extends SemiRing<D>> ITerm<D> substituteTerm(final IVariable<D> v) {
            return v;
        }

        @Override
        public ImmutableSet<IVariable<?>> getTermDomain() {
            return ImmutableCreator.create(Collections.<IVariable<?>>emptySet());
        }

        @Override
        public ImmutableSet<IVariable<?>> getTermVariablesInCodomain() {
            return ImmutableCreator.create(Collections.<IVariable<?>>emptySet());
        }

        @Override
        public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbolsInCodomain() {
            return ImmutableCreator.create(Collections.<IFunctionSymbol<?>>emptySet());
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            AbstractSubstitution.export(this.map, sb, eu, verbosityLevel);
        }

        @Override
        public PolyTermSubstitution compose(final PolyTermSubstitution sigma) {
            throw new UnsupportedOperationException("you should not do this");
        }

        @Override
        public PolyTermSubstitution termCompose(final BasicTermSubstitution sigma) {
            throw new UnsupportedOperationException("you should not do this");
        }

        @Override
        public PolyTermSubstitution polyTermCompose(final BasicTermSubstitution sigma) {
            return this.termCompose(sigma);
        }

        @Override
        public PolyTermSubstitution polyCompose(final BasicPolySubstitution sigma) {
            throw new UnsupportedOperationException("you should not do this");
        }

        @Override
        public Set<?> getDomain() {
            return this.getPolyDomain();
        }

        @Override
        public Object substitute(final Object key) {
            return this.map.get(key);
        }

        @Override
        public void addExecutionStep(final ExecutionMarkable source,
            final ExecutionMarkable target) {
            this.replaceContext.addExecutionStep(source, target);
        }

        @Override
        public ExecutionMarkable getExecutionSource(final ExecutionMarkable target) {
            return this.replaceContext.getExecutionSource(target);
        }

        @Override
        public void setExecutionMarks() {
            this.replaceContext.setExecutionMarks();
        }

    }
}
