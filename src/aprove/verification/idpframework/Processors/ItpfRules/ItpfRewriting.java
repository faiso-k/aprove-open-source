package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author mpluecke
 */
public class ItpfRewriting extends AbstractItpfReplaceRule<ReplaceContext.ReplaceContextSkeleton, ItpfConjClause, Unused> {

    public ItpfRewriting() {
        super(new ExportableString("ItpfRewriting"), new ExportableString(
            "ItpfRewriting"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return true;
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
        return CompatibleMarkClasses.I_REWRITING.isCompatible(mark);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {

        IQTermSet q = idp.getIdpGraph().getQ();
        if (atom.isItp() && positive) {
            final ItpfItp itp = (ItpfItp) atom;
            final ItpRelation relation = itp.getRelation();
            if (!itp.getL().isVariable() && relation.isRewriteRel()
                && !relation.isReflexive()) {
                final IFunctionApplication<?> faL =
                    (IFunctionApplication<?>) itp.getL();
                final ItpfFactory itpfFactory = idp.getItpfFactory();

                Itpf constructorRewritingRewrites = null;
                if (q.getPredefinedMode() == IQTermSet.PredefinedQMode.ConstructorRewriting) {
                    constructorRewritingRewrites = this.getConstructorRewritingRewrites(idp, s, itp, faL);
                }
                if (constructorRewritingRewrites != null) {
                    return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                            constructorRewritingRewrites,
                            ImplicationType.EQUIVALENT,
                            ApplicationMode.SingleStep, true);
                }

                final Itpf preDefinedRewrites = this.getPredefinedRewrites(idp, s, itp, faL);
                if (preDefinedRewrites == null) {
                    return null;
                }

                final Itpf userDefinedRewrites = this.getUserDefinedRewrites(idp, s, itp, faL);
                if (userDefinedRewrites == null) {
                    return null;
                }



                return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(
                    itpfFactory.createOr(preDefinedRewrites, userDefinedRewrites),
                    ImplicationType.EQUIVALENT,
                    ApplicationMode.SingleStep, true);
            }
        }
        return null;
    }

    private Itpf getConstructorRewritingRewrites(IDPProblem idp,
        Set<ITerm<?>> s,
        ItpfItp itp,
        IFunctionApplication<?> faL) {

        final IDependencyGraph graph = idp.getIdpGraph();
        final ItpfFactory itpfFactory = idp.getItpfFactory();
        FreshVarGenerator freshVarGen = graph.getFreshVarGenerator();

        Itpf replaceData = itpfFactory.createTrue();
        boolean successful = false;

        IFunctionApplication<?> newfaL = faL;

        Set<IVariable<?>> freshVarSet = new LinkedHashSet<>();

        if (itp.getRelation() == ItpRelation.TO_PLUS && s.contains(itp.getR())) {
            for (Pair<IPosition, ITerm<?>> posWithSubterms : faL.getPositionsWithSubTerms()) {
                if (!posWithSubterms.getValue().isVariable() && !successful) {
                    IFunctionApplication<?> fA = (IFunctionApplication<?>) posWithSubterms.getValue();
                    if (!fA.getRootSymbol().isPredefined()) {
                        int argPos = 0;
                        for (ITerm<?> arg : fA.getArguments()) {
                            if (!arg.isVariable() && PredefinedUtil.onlyPredefined(arg)) {
                                IFunctionSymbol<?> argRoot = ((IFunctionApplication<?>) arg).getRootSymbol();
                                if (argRoot.isPredefinedFunction()) {
                                    IVariable<?> freshVar = freshVarGen.getFreshVariable("rX", arg.getDomain(), false);
                                    freshVarGen.lockName(freshVar.getName());
                                    freshVarSet.add(freshVar);
                                    s.add(freshVar);
                                    final ItpfItp newItpPol =
                                        itpfFactory.createItp(arg, null, null, ItpRelation.TO_PLUS, freshVar, null,
                                            null);
                                    replaceData =
                                        itpfFactory.createAnd(replaceData,
                                            itpfFactory.create(newItpPol, true, ITerm.EMPTY_SET));
                                    newfaL =
                                        (IFunctionApplication<?>) newfaL.replaceAt(
                                            posWithSubterms.getKey().append(argPos), freshVar);
                                    successful = true;
                                }
                            }
                            argPos++;
                        }
                    }
                }
            }
        }

        if (successful) {
            final ItpfItp newItp =
                    itpfFactory.createItp(newfaL, itp.getKLeft(), itp.getContextL(), ItpRelation.TO_TRANS,
                        itp.getR(), itp.getKRight(), itp.getContextR());
            replaceData =
                    itpfFactory.createAnd(replaceData,
                        itpfFactory.create(newItp, true, ITerm.EMPTY_SET));
            replaceData = itpfFactory.quantifyExist(freshVarSet, replaceData);
            return replaceData;
        } else {
            return null;
        }
    }

    private Itpf getPredefinedRewrites(final IDPProblem idp,
        final Set<ITerm<?>> s,
        final ItpfItp itp,
        final IFunctionApplication<?> faL) {
        final IDependencyGraph graph = idp.getIdpGraph();
        final IQTermSet q = graph.getQ();
        final ItpfFactory itpfFactory = idp.getItpfFactory();
        final IDPPredefinedMap predefinedMap = idp.getPredefinedMap();

        Itpf replaceData = itpfFactory.createFalse();
        for (final Map.Entry<IFunctionSymbol<?>, Collection<Pair<IPosition, ITerm<?>>>> fsForPosWithSubterm : faL.getSortedPositionsWithSubTerms().entrySet()) {
            final IFunctionSymbol<?> fs = fsForPosWithSubterm.getKey();
            if (fs != null) {
                final PredefinedFunction<?, ?> predefinedFunction = PredefinedUtil.getPredefinedFunction(fs);
                if (predefinedFunction != null) {
                    for (final Pair<IPosition, ITerm<?>> posWithSubterm : fsForPosWithSubterm.getValue()) {
                        if (predefinedFunction.canMatchPredefLhs(posWithSubterm.y)) {

                            if (posWithSubterm.x.isEmptyPosition()) {
                                // no reduction at root
                                return null;
                            }

                            final Collection<Pair<Itpf,ITerm<?>>> possibleReductions;

                            switch (predefinedFunction.getFunc()) {
                            case Ge :
                            case Gt :
                            case Le :
                            case Lt :
                                possibleReductions = this.getPossibleReductionsRelation(predefinedMap, itpfFactory, predefinedFunction, (IFunctionApplication<?>) posWithSubterm.y);
                                break;
                            default : return null;
                            }

                            for (final Pair<Itpf,ITerm<?>> possibleReduction : possibleReductions) {
                                final ITerm<?> newItpL = itp.getL().replaceAt(posWithSubterm.x, possibleReduction.y);
                                final ItpfItp newItp = itpfFactory.createItp(newItpL, itp.getKLeft(), itp.getContextL(), ItpRelation.TO_TRANS, itp.getR(), itp.getKRight(), itp.getContextR());
                                replaceData = itpfFactory.createOr(replaceData, itpfFactory.createAnd(itpfFactory.create(newItp, true, ITerm.EMPTY_SET), possibleReduction.x));
                            }
                        }
                    }
                }
            }
        }

        return replaceData;
    }

    private Collection<Pair<Itpf, ITerm<?>>> getPossibleReductionsRelation(final IDPPredefinedMap predefinedMap, final ItpfFactory itpfFactory,
        final PredefinedFunction<?, ?> predefinedFunction,
        final IFunctionApplication<?> term) {
        final ArrayList<Pair<Itpf, ITerm<?>>> res = new ArrayList<Pair<Itpf, ITerm<?>>>(2);

        final LinkedHashSet<ITerm<?>> s = new LinkedHashSet<ITerm<?>>();
        s.addAll(term.getArguments());

        final ImmutableLinkedHashSet<ITerm<?>> immutableS = ImmutableCreator.create(s);

        // true case
        {
            final IFunctionApplication<BooleanRing> TRUE = predefinedMap.getBoolean(true).getTerm();
            final ItpfItp itpTrue = itpfFactory.createItp(term, null, null, ItpRelation.TO_TRANS, TRUE, null, null);
            res.add(new Pair<Itpf, ITerm<?>>(itpfFactory.create(itpTrue, true, immutableS), TRUE));
        }

        // false case
        {
            final IFunctionApplication<BooleanRing> FALSE = predefinedMap.getBoolean(false).getTerm();
            final ItpfItp itpFalse = itpfFactory.createItp(term, null, null, ItpRelation.TO_TRANS, FALSE, null, null);
            res.add(new Pair<Itpf, ITerm<?>>(itpfFactory.create(itpFalse, true, immutableS), FALSE));
        }

        return res;
    }

    private Itpf getUserDefinedRewrites(final IDPProblem idp,
        final Set<ITerm<?>> s,
        final ItpfItp itp,
        final IFunctionApplication<?> faL) {
        final IDependencyGraph graph = idp.getIdpGraph();
        final IQTermSet q = graph.getQ();
        final ItpfFactory itpfFactory = idp.getItpfFactory();
        final PolyFactory polyFactory = itpfFactory.getPolyFactory();
        Itpf replaceData = itpfFactory.createFalse();

        final ImmutableList<ImmutableSet<INode>> rewriteSccs = graph.getSCCs(this.filterEdges(graph.getEdges(), EdgeType.REWRITE_EDGE_TYPES));

        for (final Entry<INode, Pair<VarRenaming, Collection<Pair<IPosition, ISubstitution>>>> unifyingNode : graph.getUnifyingNodes(
            faL,
            faL.getSortedPositionsWithSubTerms(), true).entrySet()) {
            final INode node = unifyingNode.getKey();
            final ITerm<?> nodeTerm = graph.getTerm(node).applySubstitution(unifyingNode.getValue().x);

            for (final Pair<IPosition, ISubstitution> posMgu : unifyingNode.getValue().y) {
                for (final ImmutableCollection<IEdge> succEdges : graph.getSuccessors(
                    node).values()) {
                    for (final IEdge succEdge : succEdges) {
                        if (succEdge.type.isRewrite()) {
                            final LinkedHashSet<ITerm<?>> newS =
                                new LinkedHashSet<ITerm<?>>(s);

                            final ITerm<?> redex =
                                nodeTerm.getSubterm(succEdge.fromPos);

                            boolean isLegalRewrite = true;

                            if (!redex.isVariable()) {
                                for (final ITerm<?> redexArg : ((IFunctionApplication<?>) redex).getArguments()) {
                                    newS.add(redexArg);
                                }
                            } else if (q.canBeRewritten(redex)) {
                                isLegalRewrite = false;
                            }

                            if (isLegalRewrite) {
                                if (this.isNodeInScc(rewriteSccs, node)) {
                                    // abort rewriting then
                                    return null;
                                }
                                ITerm<?> succNodeTerm;
                                if (succEdge.to == succEdge.from) {
                                    succNodeTerm = graph.getTerm(succEdge.to).applySubstitution(graph.getLoopRenaming(succEdge.to));
                                } else {
                                    succNodeTerm = graph.getTerm(succEdge.to);
                                }
                                final Pair<ITerm<?>, VarRenaming> renamedSuccTerm = this.renameVariables(succNodeTerm,
                                    graph.getFreshVarGenerator(), polyFactory);

                                final ITerm<?> newLeft =
                                    itp.getL().replaceAt(
                                        posMgu.x,
                                        nodeTerm.replaceAt(
                                            succEdge.fromPos, renamedSuccTerm.x));

                                final ItpfItp newItp =
                                    itpfFactory.createItp(newLeft, itp.getKLeft(),
                                        itp.getContextL(), ItpRelation.TO_TRANS,
                                        itp.getR(), itp.getKRight(),
                                        itp.getContextR());

                                Itpf edgeCondition =
                                    graph.getCondition(succEdge).applySubstitution(
                                        renamedSuccTerm.y).applySubstitution(
                                            unifyingNode.getValue().x);

                                final VarRenaming boundVarsRenaming = ItpfUtil.getVariableRenaming(polyFactory, edgeCondition.getBoundVariables(), graph.getFreshVarGenerator());
                                edgeCondition = edgeCondition.applySubstitution(boundVarsRenaming, true);

                                final LiteralMap replacement =
                                    this.convertSubstitutionToFormula(itpfFactory,
                                        posMgu.y);
                                replacement.put(newItp, true);

                                Itpf replaceCondition =
                                    itpfFactory.createAnd(
                                        edgeCondition,
                                        itpfFactory.create(itpfFactory.createClause(
                                            ImmutableCreator.create(replacement),
                                            ImmutableCreator.create(ItpfUtil.expandS(newS)))));

                                final LinkedHashSet<IVariable<?>> freshVariables =
                                    new LinkedHashSet<IVariable<?>>(nodeTerm.getVariables());
                                freshVariables.addAll(renamedSuccTerm.x.getVariables());

                                replaceCondition = itpfFactory.quantifyExist(freshVariables, replaceCondition);

                                replaceData =
                                    itpfFactory.createOr(graph.getFreshVarGenerator(), replaceData,
                                        replaceCondition);
                            }
                        }
                    }
                }
            }
        }
        return replaceData;
    }

    private boolean isNodeInScc(final ImmutableList<ImmutableSet<INode>> rewriteSccs,
        final INode node) {
        for (final ImmutableSet<INode> scc : rewriteSccs) {
            if (scc.contains(node)) {
                return true;
            }
        }
        return false;
    }

    private Collection<IEdge> filterEdges(final ImmutableSet<IEdge> edges,
        final ImmutableSet<EdgeType> edgeTypes) {
        final LinkedHashSet<IEdge> res = new LinkedHashSet<IEdge>();
        for (final IEdge edge : edges) {
            if (edgeTypes.contains(edge.type)) {
                res.add(edge);
            }
        }

        return res;
    }

    private LiteralMap convertSubstitutionToFormula(final ItpfFactory itpfFactory,
        final BasicTermSubstitution y) {
        final LiteralMap literals = new LiteralMap();

        for (final IVariable<?> v : y.getTermDomain()) {
            literals.put(itpfFactory.createItp(v, null, null, ItpRelation.EQ, y.substituteTerm(v), null, null), true);
        }

        return literals;
    }

    private Pair<ITerm<?>, VarRenaming> renameVariables(final ITerm<?> term,
        final FreshVarGenerator freshVarGenerator, final PolyFactory polyFactory) {
        final Map<IVariable<?>, IVariable<?>> varRenamingMap = new LinkedHashMap<IVariable<?>, IVariable<?>>();

        for (final IVariable<?> var : term.getVariables()) {
            freshVarGenerator.lockName(var.getName());
            varRenamingMap.put(var, freshVarGenerator.getFreshVariable(var, false));
        }

        final VarRenaming varRenaming = VarRenaming.create(ImmutableCreator.create(varRenamingMap), true, polyFactory);

        return new Pair<ITerm<?>, VarRenaming>(term.applySubstitution(varRenaming), varRenaming);
    }

    @Override
    protected ItpfConjClause createReplaceData(final ItpfFactory itpfFactory,
        final LiteralMap conjunction, final ImmutableSet<ITerm<?>> sTerms) {
        return itpfFactory.createClause(ImmutableCreator.create(conjunction), ITerm.EMPTY_SET);
    }

    @Override
    protected aprove.verification.idpframework.Processors.ItpfRules.ReplaceContext.ReplaceContextSkeleton createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new ReplaceContext.ReplaceContextSkeleton();
    }
}