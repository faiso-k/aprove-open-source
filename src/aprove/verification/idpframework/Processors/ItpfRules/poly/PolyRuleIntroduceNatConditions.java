package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.poly.PolyRuleIntroduceNatConditions.*;
import aprove.verification.idpframework.Processors.Poly.*;
import immutables.*;

/**
 * @author MP
 */
public class PolyRuleIntroduceNatConditions extends AbstractItpfReplaceRule.ItpfReplaceRuleSkeleton<PreconditionToVarSignumCache, Unused> {

    private final BigIntSMTEngine smtEngine = new BigIntSMTEngine();

    public PolyRuleIntroduceNatConditions() {
        super(new ExportableString("[P] IntroduceNatConditions"), new ExportableString("[P] IntroduceNatConditions"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null &&
            idp.getIdpGraph().getPolyInterpretation().getRing().isSameRing(BigInt.ZERO);
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
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isSound() {
        return true;
    }

    @Override
    public boolean isAtomicMark() {
        return false;
    }

    @Override
    public boolean isClauseMark() {
        return false;
    }

    @Override
    public boolean isContextFree() {
        return false;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return mark.getClass() == this.getClass();
    }

    @Override
    protected PreconditionToVarSignumCache createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        @SuppressWarnings("unchecked")
        final PolyInterpretation<BigInt> polyInterpretation = (PolyInterpretation<BigInt>) idp.getPolyInterpretation();

        final Map<IVariable<BigInt>, IVariable<?>> polyToTermVar = new LinkedHashMap<IVariable<BigInt>, IVariable<?>>();
        for (final Map.Entry<IVariable<?>, IVariable<BigInt>> varToPolyVar : polyInterpretation.getVariableInterpretations().entrySet()) {
            final IVariable<?> oldValue = polyToTermVar.put(varToPolyVar.getValue(), varToPolyVar.getKey());
            if (Globals.useAssertions) {
                assert oldValue == null : "variable mapping must be bijective";
            }
        }

        return new PreconditionToVarSignumCache(polyToTermVar);
    }


    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processImplication(final IDPProblem idp,
        final PreconditionToVarSignumCache context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfImplication implication,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {
        ImplicationType totalExecutionRequirements = executionRequirements;
        if (!positive) {
            totalExecutionRequirements =
                totalExecutionRequirements.invert();
        }

        final ItpfFactory itpfFactory = idp.getIdpGraph().getItpfFactory();

        ItpfAndWrapper totalConclusionPrecondition;
        if (this.isAtomicMark()) {
            totalConclusionPrecondition = new ItpfAndWrapper(implication.getPrecondition(), itpfFactory);
        } else {
            totalConclusionPrecondition = precondition.addFormula(implication.getPrecondition());
        }

        final ApplicationMode remainingMode = mode;
        ApplicationMode usedApplications = ApplicationMode.NoOp;

        final ExecutionResult<Conjunction<Itpf>, Itpf> newImplConclusion =
            this.process(idp, context,
                totalConclusionPrecondition,
                implication.getConclusion(),
                totalExecutionRequirements, remainingMode,
                aborter);

        usedApplications =
            usedApplications.increaseBy(newImplConclusion.usedApplications);

        ImplicationType totalImplication;
        if (positive) {
            totalImplication = newImplConclusion.implication;
        } else {
            totalImplication = newImplConclusion.implication.invert();
        }

        if (Globals.useAssertions) {
            assert totalImplication.subsumes(executionRequirements) : "illegal result";
        }

        final Itpf renderedImplConclusion = itpfFactory.createAnd(newImplConclusion.result.asCollection());

        final ImmutableList<ItpfQuantor> renderedQuantors =
            this.getRenderedQuantors(itpfFactory, implication.getPrecondition(),
                renderedImplConclusion);

        return this.getSingletonReturn(
            itpfFactory,
            renderedQuantors,
            itpfFactory.createImplication(
                implication.getPrecondition(),
                itpfFactory.create(renderedImplConclusion.asCollection())), positive, totalImplication, usedApplications, false);
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final PreconditionToVarSignumCache context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) throws AbortionException {
        if (atom.isPoly() && executionRequirements.isComplete() && positive) {

            @SuppressWarnings("unchecked")
            final PolyInterpretation<BigInt> polyInterpretation = (PolyInterpretation<BigInt>) idp.getPolyInterpretation();
            final PolyFactory polyFactory = polyInterpretation.getFactory();
            final ItpfFactory itpfFactory = idp.getItpfFactory();
            @SuppressWarnings("unchecked")
            final
            ItpfPolyAtom<BigInt> polyAtom = (ItpfPolyAtom<BigInt>) atom;

            final Map<IVariable<BigInt>, Signum> varSignum = this.determineVarSignum(polyInterpretation, context, precondition.getFormula(), aborter);

            final LiteralMap newConditions = new LiteralMap();

            for (final IVariable<BigInt> conclusionVar : polyAtom.getPoly().getVariables()) {
                final IVariable<?> originalConclusionVar = polyInterpretation.getReverseVariableInterpretations().get(conclusionVar);
                if (originalConclusionVar != null &&
                        !polyInterpretation.isExistQuantified(conclusionVar) &&
                        originalConclusionVar.getDomain().isUserDefinedDomain()) {
                    final Signum signum = Signum.getSignum(varSignum, Collections.singletonMap(conclusionVar, BigInt.ONE));
                    if (signum == null || !signum.isDetermined()) {
                        final ItpfPolyAtom<BigInt> polyCondition = itpfFactory.createPoly(
                            polyFactory.create(conclusionVar),
                            ConstraintType.GE,
                            polyInterpretation);

                        IVariable<?> conclusionTermVar = context.getPolyVarToTermVar().get(conclusionVar);
                        if (conclusionTermVar == null) {
                            conclusionTermVar = conclusionVar;
                        }

                        final ItpfBoolPolyVar<BigInt> natPrecondition = polyInterpretation.getItpfBooleanPolyVar(ConstantType.NatDomain, conclusionTermVar.getDomain(), null);
                        newConditions.put(
                            itpfFactory.createImplication(
                                itpfFactory.create(natPrecondition, true, ITerm.EMPTY_SET),
                                itpfFactory.create(polyCondition, true, ITerm.EMPTY_SET)),
                            true);
                    }
                }
            }

            if (!newConditions.isEmpty()) {
                final ItpfImplication newImplication = itpfFactory.createImplication(
                    itpfFactory.create(
                        itpfFactory.createClause(
                            ImmutableCreator.create(newConditions),
                            ITerm.EMPTY_SET
                        )
                    ),
                    itpfFactory.create(polyAtom, positive, ITerm.EMPTY_SET));

                return this.getSingletonReturn(itpfFactory,
                    newImplication,
                    positive,
                    ImplicationType.EQUIVALENT,
                    ApplicationMode.SingleStep,
                    false);
            }
        }

        return null;
    }

    private Map<IVariable<BigInt>, Signum> determineVarSignum(final PolyInterpretation<BigInt> interpretation,
        final PreconditionToVarSignumCache context, final Itpf precondition,
        final Abortion aborter) throws AbortionException {
        Map<IVariable<BigInt>, Signum> result = context.get(precondition);
        if (result != null) {
            return result;
        }

        final Iterator<ItpfConjClause> clausesIterator =
            precondition.getClauses().iterator();

        result = new LinkedHashMap<IVariable<BigInt>, Signum>();

        // initialize result
        if (clausesIterator.hasNext()) {
            result.putAll(this.smtEngine.getVarSignum(clausesIterator.next(),
                interpretation, aborter));
        }

        // just keep intersection of var signums
        if (clausesIterator.hasNext() && !result.isEmpty()) {
            final Map<IVariable<BigInt>, Signum> clauseVarSignum = this.smtEngine.getVarSignum(clausesIterator.next(),
                interpretation, aborter);
            final Iterator<Entry<IVariable<BigInt>, Signum>> resultIterator =
                result.entrySet().iterator();

            while (resultIterator.hasNext()) {
                final Entry<IVariable<BigInt>, Signum> resultSignumEntry = resultIterator.next();
                final Signum clauseSignum = clauseVarSignum.get(resultSignumEntry.getKey());
                if (clauseSignum != null) {
                    resultSignumEntry.setValue(clauseSignum.lessSpecific(resultSignumEntry.getValue()));
                } else {
                    resultIterator.remove();
                }
            }
        }

        context.put(precondition, result);

        return result;
    }

    protected static class PreconditionToVarSignumCache extends ReplaceContext.ReplaceContextSkeleton {

        private final Map<IVariable<BigInt>, IVariable<?>> polyVarToTermVar;
        private final HashMap<Itpf, Map<IVariable<BigInt>, Signum>> cache;

        public PreconditionToVarSignumCache(final Map<IVariable<BigInt>, IVariable<?>> polyVarToTermVar) {
            this.polyVarToTermVar = polyVarToTermVar;
            this.cache = new HashMap<Itpf, Map<IVariable<BigInt>, Signum>>();
        }

        public void put(final Itpf precondition, final Map<IVariable<BigInt>, Signum> result) {
            this.cache.put(precondition, result);
        }

        public Map<IVariable<BigInt>, Signum> get(final Itpf precondition) {
            return this.cache.get(precondition);
        }

        public Map<IVariable<BigInt>, IVariable<?>> getPolyVarToTermVar() {
            return this.polyVarToTermVar;
        }

    }

}
