package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.ItpfAtomReplaceData.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public abstract class AbstractItpfReplaceRule<ContextType extends ReplaceContext, R extends ItpfAtomReplaceData, MetaDataType>
    extends
        GenericItpfRule.GenericItpfRuleSkeleton<MetaDataType> implements GenericItpfRule<MetaDataType>
{

    protected final GenericItpfRule<MetaDataType> mark;
    private final ImmutableArrayList<Mark<?>> usedMarks;

    public AbstractItpfReplaceRule(final ExportableString shortDescription, final ExportableString longDescription) {
        super(shortDescription, longDescription);
        this.mark = this;
        final ArrayList<Mark<?>> tmp = new ArrayList<Mark<?>>(1);
        tmp.add(this.mark);
        this.usedMarks = ImmutableCreator.create(tmp);
    }

    @Override
    public boolean isApplicable(final IDPProblem idp, final Itpf formula, final ApplicationMode mode) {
        return this.isApplicable(idp) && !MarksHandler.isMarkedFail(this.mark, formula);
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return this.usedMarks;
    }

    @Override
    public ExecutionResult<Conjunction<Itpf>, Itpf> process(
        final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException
    {
        final ContextType context = this.createContext(idp, precondition, formula, executionRequirements, mode, aborter);
        final ExecutionResult<Conjunction<Itpf>, Itpf> result =
            this.process(idp, context, precondition, formula, executionRequirements, mode, aborter);

        final ExecutionResult<Conjunction<Itpf>, Itpf> postProcessed =
            this.postProcess(idp, context, precondition, result, executionRequirements, mode, aborter);
        context.setExecutionMarks();

        return postProcessed;
    }

    protected ExecutionResult<Conjunction<Itpf>, Itpf> postProcess(
        final IDPProblem idp,
        final ContextType context,
        final ItpfAndWrapper precondition,
        final ExecutionResult<Conjunction<Itpf>, Itpf> result,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter)
    {
        return result;
    }

    protected ExecutionResult<Conjunction<Itpf>, Itpf> process(
        final IDPProblem idp,
        final ContextType context,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException
    {
        final ItpfFactory itpfFactory = idp.getIdpGraph().getItpfFactory();

        boolean changed = false;
        ApplicationMode remainingMode = mode;
        ApplicationMode usedApplications = ApplicationMode.NoOp;
        ImplicationType totalImplication = ImplicationType.EQUIVALENT;

        final List<ItpfQuantor> newQuantors = new ArrayList<ItpfQuantor>();

        final Set<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>(formula.getClauses().size());

        boolean fixpointReached = true;

        for (final ItpfConjClause c : formula.getClauses()) {
            assert formula.getQuantification().isEmpty() : "formula must not contain quantification";

            final ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> preProcessingResult =
                this.preProcessClause(idp, context, precondition, c, executionRequirements, remainingMode, aborter);

            remainingMode = mode.decreaseBy(preProcessingResult.usedApplications);
            usedApplications = usedApplications.increaseBy(preProcessingResult.usedApplications);
            totalImplication = totalImplication.mult(preProcessingResult.implication);

            changed = changed || !preProcessingResult.isSingleton(c);

            for (final ItpfConjClause clause : preProcessingResult.result) {
                // processing a single clause
                if (remainingMode == ApplicationMode.NoOp) {
                    newClauses.add(clause);
                    fixpointReached = false;
                } else {
                    final ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> clausesResult =
                        this.processClause(
                            idp,
                            context,
                            precondition,
                            preProcessingResult.result.getQuantification(),
                            clause,
                            formula,
                            executionRequirements,
                            remainingMode,
                            aborter);

                    fixpointReached = fixpointReached && clausesResult.fixpointReached;

                    if (clausesResult.result.size() != 1 || clausesResult.result.iterator().next() != clause) {
                        changed = true;
                    }

                    remainingMode = remainingMode.decreaseBy(clausesResult.usedApplications);
                    usedApplications = usedApplications.increaseBy(clausesResult.usedApplications);
                    final ImplicationType backup = totalImplication;
                    if (Globals.useAssertions) {
                        assert totalImplication.mult(clausesResult.implication).subsumes(executionRequirements);
                    }

                    totalImplication = totalImplication.mult(clausesResult.implication);

                    if (totalImplication == ImplicationType.UNRELATED) {
                        assert false : backup;
                    }

                    newQuantors.addAll(clausesResult.result.getQuantification());
                    newClauses.addAll(clausesResult.result.asCollection());
                }
                aborter.checkAbortion();
            }

            aborter.checkAbortion();
        }

        if (changed) {
            final Itpf newFormula;
            if (newClauses.isEmpty()) {
                newFormula = itpfFactory.createFalse();
            } else {
                newFormula =
                    itpfFactory.create(ImmutableCreator.create(newQuantors), ImmutableCreator.create(newClauses));
            }

            final ExecutionResult<Conjunction<Itpf>, Itpf> result =
                new ExecutionResult<Conjunction<Itpf>, Itpf>(
                    new Conjunction<Itpf>(newFormula),
                    totalImplication,
                    usedApplications,
                    fixpointReached);
            if (totalImplication == ImplicationType.UNRELATED) {
                assert false;
            }
            return result;
        } else {
            final ExecutionResult<Conjunction<Itpf>, Itpf> result =
                new ExecutionResult<Conjunction<Itpf>, Itpf>(
                    new Conjunction<Itpf>(formula),
                    ImplicationType.EQUIVALENT,
                    usedApplications,
                    true);
            return result;
        }
    }

    protected abstract ContextType createContext(
        final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter);

    private ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> processClause(
        final IDPProblem idp,
        final ContextType context,
        final ItpfAndWrapper precondition,
        final List<ItpfQuantor> clauseQuantification,
        final ItpfConjClause clause,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException
    {

        final ExecutionMark<MetaDataType> executionMark;

        if (context == null && this.isClauseMark()) {
            executionMark =
                new ExecutionMark<MetaDataType>(this.mark, idp.getPolyInterpretation(), executionRequirements, mode);

            final ImmutablePair<ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>, MetaDataType> clauseMark =
                clause.getMarks().getMark(executionMark);

            if (clauseMark != null) {
                return clauseMark.x;
            }
        } else {
            executionMark = null;
        }

        final ImmutableMap<? extends ItpfAtom, Boolean> literals = clause.getLiterals();

        // initialize processing que, start with clause literals and process all of them
        final LinkedList<ProcessEntry> processing = new LinkedList<ProcessEntry>();

        processing.add(new ProcessEntry(
            new ArrayList<ItpfQuantor>(clauseQuantification),
            new LiteralMap(literals),
            new LinkedHashSet<ITerm<?>>(clause.getS()),
            new LinkedList<ItpfAtom>(literals.keySet())));

        // this will hold all complete processings
        final LinkedList<ProcessResult> processed = new LinkedList<ProcessResult>();

        // set to true, if any changes are made
        boolean changedClause = false;

        ApplicationMode remainingApplications = mode;
        ApplicationMode usedApplications = ApplicationMode.NoOp;
        ImplicationType totalImplication = ImplicationType.EQUIVALENT;

        boolean fixpointReached = true;

        while (!processing.isEmpty()) {
            // process a single processing step
            final ProcessEntry process = processing.poll();

            // process all atoms in this processing step
            boolean changedProcess = false;
            while (!process.literalsToProcess.isEmpty()
                && remainingApplications != ApplicationMode.NoOp
                && !process.literals.isUnsatisfiable())
            {
                final ItpfAtom atom = process.literalsToProcess.poll();
                final Boolean value = process.literals.remove(atom);

                // value == null if we process an atom which has already been removed, nothing to do then
                if (value != null) {
                    // call abstract method and get atoms which replace given atom
                    final ExecutionResult<? extends QuantifiedDisjunction<R>, R> result =
                        this.processImplicationOrLiteral(
                            idp,
                            context,
                            precondition,
                            process.literals,
                            process.sTerms,
                            atom,
                            value,
                            executionRequirements,
                            mode,
                            aborter);

                    // if result == null, no replacing should be done
                    if (result != null) {
                        if (Globals.useAssertions) {
                            assert result.implication.subsumes(executionRequirements) : "illegal result";
                        }
                        remainingApplications = remainingApplications.decreaseBy(result.usedApplications);
                        usedApplications = usedApplications.increaseBy(result.usedApplications);
                        totalImplication = totalImplication.mult(result.implication);

                        if (result.isEmpty()) {
                            process.literals.unsatisfiable();
                            changedProcess = true;
                            changedClause = true;
                            continue;
                        }

                        final Iterator<R> newClauseDatas = result.iterator();
                        // iterate over the or-replacings
                        newClauses: while (newClauseDatas.hasNext()) {
                            final ItpfAtomReplaceData newClauseData = newClauseDatas.next();

                            final LiteralMap newLiterals;
                            final List<ItpfQuantor> newQuantors;

                            final LinkedHashSet<ITerm<?>> newS = new LinkedHashSet<ITerm<?>>(process.sTerms);
                            newS.addAll(newClauseData.getS());

                            final LinkedList<ItpfAtom> literalsToProcess;
                            // create new processings for each or exept the last one, reuse current processing for this
                            if (newClauseDatas.hasNext()) {
                                newQuantors = new ArrayList<ItpfQuantor>(process.quantification);
                                newLiterals = new LiteralMap(process.literals);
                                literalsToProcess = new LinkedList<ItpfAtom>(process.literalsToProcess);
                            } else {
                                newQuantors = process.quantification;
                                newLiterals = process.literals;
                                literalsToProcess = process.literalsToProcess;
                            }

                            boolean readdedLit = false;
                            // add new literals to current literal map
                            for (final Map.Entry<? extends ItpfAtom, Boolean> newLit : newClauseData) {
                                final Boolean oldVal = newLiterals.put(newLit.getKey(), newLit.getValue());
                                if (!newLit.getKey().isImplication()) {
                                    this.markExecution(atom, newLit.getKey(), context);
                                }

                                if (oldVal != null) {
                                    if (!oldVal.equals(newLit.getValue())) {
                                        // we have an unsatisfiable clause
                                        changedClause = true;
                                        continue newClauses;
                                    }
                                    // we just added an already existing literal
                                } else {
                                    if (newLit.getKey().equals(atom) && newLit.getValue().equals(value)) {
                                        // we added the old literal again
                                        readdedLit = true;
                                    } else {
                                        // we added a new lieral
                                        changedClause = true;
                                        changedProcess = true;
                                        // should we reprocess the new literal?
                                        if (!result.fixpointReached) {
                                            literalsToProcess.addFirst(newLit.getKey());
                                        }
                                    }
                                }
                            }

                            if (!readdedLit && newClauseData.isEmpty()) {
                                this.markExecution(atom, null, context);
                            }

                            newQuantors.addAll(result.result.getQuantification());

                            changedClause =
                                changedClause || !readdedLit || !result.result.getQuantification().isEmpty();
                            changedProcess =
                                changedProcess || !readdedLit || !result.result.getQuantification().isEmpty();

                            if (newClauseDatas.hasNext()) {
                                // add new clauses as new processing step
                                processing
                                    .addFirst(new ProcessEntry(newQuantors, newLiterals, newS, literalsToProcess));
                            }
                        }
                    } else {
                        process.literals.put(atom, value);
                    }
                    aborter.checkAbortion();
                }
            }

            // we are done with processing step
            fixpointReached =
                fixpointReached && (process.literalsToProcess.isEmpty() || process.literals.isUnsatisfiable());
            if (!process.literals.isUnsatisfiable()) {
                processed.add(new ProcessResult(ImmutableCreator.create(process.quantification), ImmutableCreator
                    .create(process.literals), ImmutableCreator.create(process.sTerms)));
            }
        }

        final ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> postProcessdClause;

        final ItpfFactory itpfFactory = idp.getIdpGraph().getItpfFactory();
        if (changedClause) {
            final List<ItpfQuantor> totalClauseQuantifications = new ArrayList<ItpfQuantor>();
            final Set<ItpfConjClause> newClauses = new LinkedHashSet<ItpfConjClause>();

            for (final ProcessResult newClause : processed) {
                final ItpfConjClause c = itpfFactory.createClause(newClause.literals, newClause.sTerms);

                final ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> processResult =
                    this.postProcessClause(
                        idp,
                        context,
                        precondition,
                        newClause.quantification,
                        c,
                        executionRequirements,
                        remainingApplications,
                        aborter);

                totalClauseQuantifications.addAll(processResult.result.getQuantification());
                newClauses.addAll(processResult.result.asCollection());

                fixpointReached = fixpointReached && processResult.fixpointReached;

                totalImplication = totalImplication.mult(processResult.implication);
                usedApplications = usedApplications.increaseBy(processResult.usedApplications);
            }

            postProcessdClause =
                new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                    new QuantifiedDisjunction<ItpfConjClause>(
                        ItpfUtil.cleanupQuantors(totalClauseQuantifications),
                        ImmutableCreator.create(newClauses)), totalImplication, usedApplications, fixpointReached);
        } else {
            postProcessdClause =
                this.postProcessClause(
                    idp,
                    context,
                    precondition,
                    ItpfFactory.EMPTY_QUANTORS,
                    clause,
                    executionRequirements,
                    remainingApplications,
                    aborter).multImplication(totalImplication).increaseUsedApplications(
                    usedApplications,
                    fixpointReached);
            ;

        }

        if (Globals.useAssertions) {
            assert totalImplication.subsumes(executionRequirements) : "illegal result";
        }

        if (context == null && this.isClauseMark()) {
            MarksHandler.setExecutionMark(executionMark, clause, postProcessdClause);
        }

        return postProcessdClause;
    }

    protected ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> preProcessClause(
        final IDPProblem idp,
        final ContextType context,
        final ItpfAndWrapper precondition,
        final ItpfConjClause c,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException
    {
        return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
            new QuantifiedDisjunction<ItpfConjClause>(ItpfFactory.EMPTY_QUANTORS, c),
            ImplicationType.EQUIVALENT,
            ApplicationMode.NoOp,
            true);
    }

    protected ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> postProcessClause(
        final IDPProblem idp,
        final ContextType context,
        final ItpfAndWrapper precondition,
        final ImmutableList<ItpfQuantor> clauseQuantification,
        final ItpfConjClause c,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException
    {
        return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
            new QuantifiedDisjunction<ItpfConjClause>(clauseQuantification, c),
            ImplicationType.EQUIVALENT,
            ApplicationMode.NoOp,
            true);
    }

    protected ExecutionResult<? extends QuantifiedDisjunction<R>, R> processImplicationOrLiteral(
        final IDPProblem idp,
        final ContextType context,
        final ItpfAndWrapper precondition,
        final Map<ItpfAtom, Boolean> otherLiterals,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException
    {
        ItpfAndWrapper totalPrecondition = null;

        if (!this.isAtomicMark()) {

            final ItpfFactory itpfFactory = idp.getIdpGraph().getItpfFactory();

            final LiteralMap otherPreconditionLiterals = new LiteralMap(otherLiterals);
            otherPreconditionLiterals.remove(atom);

            final ItpfConjClause otherPreconditionClause =
                itpfFactory.createClause(ImmutableCreator.create(otherPreconditionLiterals), ITerm.EMPTY_SET);

            totalPrecondition =
                precondition.addFormula(new QuantifiedDisjunction<ItpfConjClause>(otherPreconditionClause));
        }

        if (atom.isImplication()) {
            final ItpfImplication implication = (ItpfImplication) atom;

            return this.processImplication(
                idp,
                context,
                totalPrecondition,
                s,
                implication,
                positive,
                executionRequirements,
                mode,
                aborter);
        } else {
            if (!this.isAtomicMark()) {
                totalPrecondition = precondition;
            }
            return this.processLiteral(
                idp,
                context,
                totalPrecondition,
                s,
                atom,
                positive,
                executionRequirements,
                mode,
                aborter);
        }
    }

    protected ExecutionResult<? extends QuantifiedDisjunction<R>, R> processImplication(
        final IDPProblem idp,
        final ContextType context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfImplication implication,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException
    {
        ImplicationType totalExecutionRequirements = executionRequirements;
        if (!positive) {
            totalExecutionRequirements = totalExecutionRequirements.invert();
        }

        final ItpfFactory itpfFactory = idp.getIdpGraph().getItpfFactory();

        ItpfAndWrapper totalPreconditionPrecondition;
        if (this.isAtomicMark()) {
            totalPreconditionPrecondition = null;
        } else {
            totalPreconditionPrecondition = precondition;
        }

        final ExecutionResult<Conjunction<Itpf>, Itpf> newImplPrecondition =
            this.process(
                idp,
                context,
                totalPreconditionPrecondition,
                implication.getPrecondition(),
                totalExecutionRequirements.invert(),
                mode,
                aborter);

        final ApplicationMode remainingMode = mode.decreaseBy(newImplPrecondition.usedApplications);
        ApplicationMode usedApplications = newImplPrecondition.usedApplications;
        ImplicationType totalImplication;
        if (positive) {
            totalImplication = newImplPrecondition.implication.invert();
        } else {
            totalImplication = newImplPrecondition.implication;
        }

        if (Globals.useAssertions) {
            assert totalImplication.subsumes(executionRequirements) : "illegal result";
        }

        ItpfAndWrapper totalConclusionPrecondition;
        if (this.isAtomicMark()) {
            totalConclusionPrecondition = new ItpfAndWrapper(newImplPrecondition.result.asCollection(), itpfFactory);
        } else {
            totalConclusionPrecondition = precondition.addFormulas(newImplPrecondition.result.asCollection());
        }

        final ExecutionResult<Conjunction<Itpf>, Itpf> newImplConclusion =
            this.process(
                idp,
                context,
                totalConclusionPrecondition,
                implication.getConclusion(),
                totalExecutionRequirements,
                remainingMode,
                aborter);

        usedApplications = usedApplications.increaseBy(newImplConclusion.usedApplications);

        if (positive) {
            totalImplication = totalImplication.mult(newImplConclusion.implication);
        } else {
            totalImplication = totalImplication.mult(newImplConclusion.implication.invert());
        }

        if (Globals.useAssertions) {
            assert totalImplication.subsumes(executionRequirements) : "illegal result";
        }

        final Itpf renderedImplPrecondition = itpfFactory.createAnd(newImplPrecondition.result.asCollection());
        final Itpf renderedImplConclusion = itpfFactory.createAnd(newImplConclusion.result.asCollection());

        final ImmutableList<ItpfQuantor> renderedQuantors =
            this.getRenderedQuantors(itpfFactory, renderedImplPrecondition, renderedImplConclusion);

        return this.getSingletonReturn(
            itpfFactory,
            renderedQuantors,
            itpfFactory.createImplication(
                itpfFactory.create(renderedImplPrecondition.asCollection()),
                itpfFactory.create(renderedImplConclusion.asCollection())),
            positive,
            totalImplication,
            usedApplications,
            false);
    }

    protected ImmutableList<ItpfQuantor> getRenderedQuantors(
        final ItpfFactory itpfFactory,
        final Itpf renderedImplPrecondition,
        final Itpf renderedImplConclusion)
    {
        final ImmutableList<ItpfQuantor> renderedQuantors;

        if (renderedImplPrecondition.getQuantification().isEmpty()
            && renderedImplConclusion.getQuantification().isEmpty())
        {
            renderedQuantors = ItpfFactory.EMPTY_QUANTORS;
        } else {
            final ArrayList<ItpfQuantor> rq =
                new ArrayList<ItpfQuantor>(renderedImplPrecondition.getQuantification().size()
                    + renderedImplConclusion.getQuantification().size());
            for (final ItpfQuantor precondQuantor : renderedImplPrecondition.getQuantification()) {
                rq.add(itpfFactory.createQuantor(!precondQuantor.isUniversalQuantor(), precondQuantor.getVariable()));
            }
            rq.addAll(renderedImplConclusion.getQuantification());
            renderedQuantors = ImmutableCreator.create(rq);
        }
        return renderedQuantors;
    }

    /**
     * @param idp
     * @param context
     * @param atom The atom to process.
     * @param positive True iff the literal is positive.
     * @param executionRequirements
     * @param aborter
     * @return null, if nothing to be changed or (x: new literal map the given
     * literal should be exchanged with. y: true iff new literals must be
     * reprocessed).
     * @throws AbortionException TODO
     */
    protected abstract ExecutionResult<? extends QuantifiedDisjunction<R>, R> processLiteral(
        IDPProblem idp,
        ContextType context,
        ItpfAndWrapper precondition,
        Set<ITerm<?>> s,
        final ItpfAtom atom,
        Boolean positive,
        ImplicationType executionRequirements,
        ApplicationMode mode,
        Abortion aborter) throws AbortionException;

    protected ExecutionResult<QuantifiedDisjunction<R>, R> getUnsatReturn(
        final ImplicationType implication,
        final ApplicationMode usedApplications)
    {
        return new ExecutionResult<QuantifiedDisjunction<R>, R>(
            new QuantifiedDisjunction<R>(),
            implication,
            usedApplications,
            true);
    }

    protected ExecutionResult<QuantifiedDisjunction<R>, R> getEmptyReturn(
        final ItpfFactory itpfFactory,
        final ImplicationType implication,
        final ApplicationMode usedApplications)
    {
        final LiteralMap trueSet = new LiteralMap(false);
        return this.createReplaceData(itpfFactory, ItpfFactory.EMPTY_QUANTORS, trueSet, implication, usedApplications, false);
    }

    protected ExecutionResult<QuantifiedDisjunction<R>, R> getSingletonReturn(
        final ItpfFactory itpfFactory,
        final ItpfAtom atom,
        final Boolean value,
        final ImplicationType implication,
        final ApplicationMode usedApplications,
        final Boolean reprocess)
    {
        return this.createReplaceData(
            itpfFactory,
            ItpfFactory.EMPTY_QUANTORS,
            new LiteralMap(atom, value),
            implication,
            usedApplications,
            reprocess);
    }

    protected ExecutionResult<QuantifiedDisjunction<R>, R> getSingletonReturn(
        final ItpfFactory itpfFactory,
        final ImmutableList<ItpfQuantor> newQuantification,
        final ItpfAtom atom,
        final Boolean value,
        final ImplicationType implication,
        final ApplicationMode usedApplications,
        final Boolean reprocess)
    {
        return this.createReplaceData(
            itpfFactory,
            newQuantification,
            new LiteralMap(atom, value),
            implication,
            usedApplications,
            reprocess);
    }

    protected ExecutionResult<QuantifiedDisjunction<R>, R> getAndReturn(
        final ItpfFactory itpfFactory,
        final ImmutableList<ItpfQuantor> newQuantification,
        final Boolean value,
        final ImplicationType implication,
        final ApplicationMode usedApplications,
        final Boolean reprocess,
        final ItpfAtom... atoms)
    {
        final LiteralMap map = new LiteralMap();
        for (final ItpfAtom atom : atoms) {
            map.put(atom, value);
        }
        return this.createReplaceData(itpfFactory, newQuantification, map, implication, usedApplications, reprocess);
    }

    protected final ExecutionResult<QuantifiedDisjunction<R>, R> createReplaceData(
        final ItpfFactory itpfFactory,
        final ImmutableList<ItpfQuantor> newQuantification,
        final LiteralMap conjunction,
        final ImplicationType implication,
        final ApplicationMode usedApplications,
        final Boolean reprocess)
    {
        if (conjunction.isUnsatisfiable()) {
            return this.getUnsatReturn(implication, usedApplications);
        }

        return new ExecutionResult<QuantifiedDisjunction<R>, R>(new QuantifiedDisjunction<R>(
            newQuantification,
            this.createReplaceData(itpfFactory, conjunction, ITerm.EMPTY_SET)), implication, usedApplications, !reprocess);
    }

    protected final ExecutionResult<QuantifiedDisjunction<R>, R> createReplaceData(
        final ImmutableList<ItpfQuantor> newQuantification,
        final ImmutableCollection<R> replaceData,
        final ImplicationType implication,
        final ApplicationMode usedApplications,
        final Boolean reprocess)
    {
        return new ExecutionResult<QuantifiedDisjunction<R>, R>(new QuantifiedDisjunction<R>(
            newQuantification,
            replaceData), implication, usedApplications, !reprocess);
    }

    protected void markExecution(
        final ExecutionMarkable source,
        final ExecutionMarkable target,
        final ReplaceContext context)
    {
        if (source == target) {
            // do nothing
        } else if (target != null) {
            context.addExecutionStep(source, target);
        } else {
            final ExecutionUid execUid = ExecutionUid.create(true);
            source.addExecutionMark(execUid);
        }
    }

    protected abstract R createReplaceData(
        ItpfFactory itpfFactory,
        LiteralMap conjunction,
        ImmutableSet<ITerm<?>> sTerms);

    private static class ProcessEntry {

        public LiteralMap literals;

        public Set<ITerm<?>> sTerms;

        public LinkedList<ItpfAtom> literalsToProcess;

        public List<ItpfQuantor> quantification;

        public ProcessEntry(
            final List<ItpfQuantor> quantification,
            final LiteralMap literalMap,
            final Set<ITerm<?>> sTerms,
            final LinkedList<ItpfAtom> literalsToProcess)
        {
            this.quantification = quantification;
            this.literals = literalMap;
            this.sTerms = sTerms;
            this.literalsToProcess = literalsToProcess;
        }
    }

    private static class ProcessResult {

        public ImmutableMap<ItpfAtom, Boolean> literals;

        public ImmutableSet<ITerm<?>> sTerms;

        public ImmutableList<ItpfQuantor> quantification;

        public ProcessResult(
            final ImmutableList<ItpfQuantor> quantification,
            final ImmutableMap<ItpfAtom, Boolean> literalMap,
            final ImmutableSet<ITerm<?>> sTerms)
        {
            this.quantification = quantification;
            this.literals = literalMap;
            this.sTerms = sTerms;
        }

    }

    public static abstract class ItpfReplaceRuleSkeleton<ContextType extends ReplaceContext, MetaDataType>
        extends
            AbstractItpfReplaceRule<ContextType, ItpfAtomReplaceData, Unused>
    {

        public ItpfReplaceRuleSkeleton(final ExportableString shortDescription, final ExportableString longDescription) {
            super(shortDescription, longDescription);
        }

        @Override
        protected ItpfAtomReplaceData createReplaceData(
            final ItpfFactory itpfFactory,
            final LiteralMap conjunction,
            final ImmutableSet<ITerm<?>> sTerms)
        {
            return new LiteralMapData(conjunction, sTerms);
        }

    }
}
