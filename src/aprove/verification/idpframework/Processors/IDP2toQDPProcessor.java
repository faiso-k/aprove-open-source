package aprove.verification.idpframework.Processors;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.Domain;
import aprove.verification.dpframework.IDPProblem.PfManager.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.idpframework.Algorithms.Unification.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPProblem;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.IDPPredefinedMap;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.DomainFactory;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class IDP2toQDPProcessor extends TIDPProcessor<Result> {

    public static Pair<ITerm<?>, ITerm<?>> getPolyAtomCondition(final ItpfPolyAtom<?> polyAtom, final Set<IVariable<?>> leftVars, final Set<IVariable<?>> rightVars, final IDPPredefinedMap predefinedMap) {
        if (polyAtom.getConstraintType() == ConstraintType.EQ) {
            return IDP2toQDPProcessor.getEquationCondition(leftVars, rightVars,
                polyAtom.getPoly(), predefinedMap);
        } else {
            return null;
        }
    }

    private static <C extends SemiRing<C>> Pair<ITerm<?>, ITerm<?>> getEquationCondition(final Set<IVariable<?>> fromITermVars,
        final Set<IVariable<?>> toITermVars,
        final Polynomial<C> poly, final IDPPredefinedMap predefinedMap) {
        IVariable<?> instantiatedVariable = null;
        boolean negate = false;

        final Map<Monomial<C>, C> instantitation = new LinkedHashMap<Monomial<C>, C>();
        for (final Map.Entry<? extends Monomial<C>, ? extends C> monomialCoeff : poly.getMonomials().entrySet()) {
            final Monomial<C> monomial = monomialCoeff.getKey();
            final C coeff = monomialCoeff.getValue();
            if (fromITermVars.containsAll(monomial.getVariables())) {
                instantitation.put(monomial, monomialCoeff.getValue());
            } else {
                if (instantiatedVariable == null
                        && monomial.isRealVariable() && toITermVars.contains(monomial.getRealVariable())
                        && (coeff.isOne() || coeff.negate().isOne())) {
                    instantiatedVariable = monomial.getRealVariable();
                    negate = coeff.isOne();
                } else {
                    instantiatedVariable = null;
                    break;
                }
            }
        }

        if (instantiatedVariable != null) {
            Polynomial<C> instantiatedPoly =
                poly.getFactory().create(poly.getRing(), ImmutableCreator.create(instantitation));
            if (negate) {
                instantiatedPoly = instantiatedPoly.negate();
            }

            return new Pair<ITerm<?>, ITerm<?>>(instantiatedPoly.toTerm(predefinedMap), instantiatedVariable);
        } else {
            return null;
        }
    }


    private final int limit;
    private final ToTermApplicability apply;

    @ParamsViaArgumentObject
    public IDP2toQDPProcessor(final Arguments arguments) {
        super("IDP2toQDPProcessor");
        this.apply = arguments.apply;
        this.limit = arguments.limit;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(final TIDPProblem idp, final Abortion aborter)
    throws AbortionException {
        QDPProblem qdp;
        try {
            qdp = this.IDPtoQDP(idp, aborter);
            return ResultFactory.proved(qdp, YNMImplication.SOUND, new IDPtoQDPProof(qdp));
        } catch (final UnsupportedOperationException e) {
            return ResultFactory.unsuccessful(e.getMessage());
        } catch (final IntOutOfRangeException e) {
            return ResultFactory.unsuccessful("IntOutOfRangeException");
        }
    }

    private QDPProblem IDPtoQDP(final TIDPProblem idp, final Abortion aborter) throws IntOutOfRangeException {
        final aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap convertedPredefinedMap = this.convertPredefinedMap(idp);

        // Use linked sets here just for user-friendliness. We want the
        // transformed "real" rules first and the generated rules last.
        final Set<TRSFunctionApplication> explicitOrigQTerms =
            this.<TRSFunctionApplication>convertToIDPv1Term(idp.getIdpGraph().getQ().getUserDefinedTerms());

        // beware of name clashes
        final Set<HasFunctionSymbols> forbiddenSymbols =
            new LinkedHashSet<HasFunctionSymbols>();
        forbiddenSymbols.addAll(explicitOrigQTerms);
        forbiddenSymbols.addAll(this.convertFunctionSymbol(idp.getIdpGraph().getFunctionSymbols()));

        final FreshNameGenerator freshNames = new FreshNameGenerator(CollectionUtils.getFunctionSymbols(forbiddenSymbols), FreshNameGenerator.PROLOG_VARS);
        final PredefinedFunctionsManagerNegPos npMan =
            PredefinedFunctionsManagerNegPos.create(
                convertedPredefinedMap, freshNames,
                this.limit);

        final Set<TRSFunctionApplication> qTerms =
            this.createQdpQTerms(explicitOrigQTerms, npMan);

        final Pair<Set<Rule>, Graph<Rule, ?>> convertedGraph = this.convertIDPGraph(idp, convertedPredefinedMap, npMan, freshNames, qTerms);

        // The generated rules do not add new PAIRS, but we need to add the
        // rules generated for the PAIRS to the RULES section too.

        final Set<Rule> rules = new LinkedHashSet<Rule>();
        rules.addAll(convertedGraph.x);

        final Set<Rule> rulesForPredefs = npMan.getGeneratedRules();
        rules.addAll(rulesForPredefs);
        qTerms.addAll(CollectionUtils.getLeftHandSides(rulesForPredefs));

        return QDPProblem.create(convertedGraph.y,
            QTRSProblem.create(ImmutableCreator.create(rules), qTerms),
            idp.isMinimal());
    }

    private Pair<Set<Rule>, Graph<Rule, ?>> convertIDPGraph(final IDPProblem idp,
        final aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap convertedPredefinedMap,
        final PredefinedFunctionsManagerNegPos npMan,
        final FreshNameGenerator freshNames,
        final Set<TRSFunctionApplication> qTerms) throws IntOutOfRangeException {
        final IDependencyGraph idpGraph = idp.getIdpGraph();

        final Graph<Rule, ?> qdpGraph = new Graph<Rule, Object>();
        final Set<Rule> rules = new LinkedHashSet<Rule>();
        final Map<FunctionSymbol, FunctionSymbol> sharpSymbolMap = this.createSharpSymbolMap(idp.getIdpGraph(), convertedPredefinedMap, npMan, freshNames);

        final CollectionMap<Node<Rule>, IEdge> nodeSucceccors = new CollectionMap<Node<Rule>, IEdge>();
        final Map<IEdge, Set<Node<Rule>>> infEdgeEntryNodes = new LinkedHashMap<IEdge, Set<Node<Rule>>>();

        for (final Entry<IEdge, Itpf> edgeCondition : idpGraph.getEdgeConditions().entrySet()) {
            final IEdge edge = edgeCondition.getKey();

            final List<List<Rule>> convertedEdge = this.convertEdge(idp, convertedPredefinedMap, npMan, freshNames,
                sharpSymbolMap, qTerms, edge, edgeCondition.getValue());

            if (edge.type.isRewrite()) {
                for (final List<Rule> ruleList : convertedEdge) {
                    rules.addAll(ruleList);
                }
            }

            if (edge.type.isInf()) {
                final Set<Node<Rule>> entryNodes =
                    this.linkInfEdge(idpGraph, qdpGraph, sharpSymbolMap,
                        nodeSucceccors, edge, convertedEdge);

                infEdgeEntryNodes.put(edge, entryNodes);
            }
        }

        this.linkQDPGraph(qdpGraph, nodeSucceccors, infEdgeEntryNodes);

        return new Pair<Set<Rule>, Graph<Rule,?>>(rules, qdpGraph);
    }

    private Set<Node<Rule>> linkInfEdge(final IDependencyGraph idpGraph,
        final Graph<Rule, ?> qdpGraph,
        final Map<FunctionSymbol, FunctionSymbol> sharpSymbolMap,
        final CollectionMap<Node<Rule>, IEdge> nodeSucceccors,
        final IEdge edge,
        final List<List<Rule>> convertedEdge) {
        final Set<Node<Rule>> entryNodes = new LinkedHashSet<Node<Rule>>();

        for (final List<Rule> ruleList : convertedEdge) {
            Node<Rule> lastRuleNode = null;
            final ListIterator<Rule> ruleIterator = ruleList.listIterator();
            while(ruleIterator.hasNext()) {
                final Rule rule = ruleIterator.next();
                if (ruleIterator.hasNext()) {
                    final Rule sharpedRule = this.getSharpedRule(
                        rule,
                        sharpSymbolMap,
                        ruleIterator.previousIndex() == 0,
                        false);
                    final Node<Rule> ruleNode = new Node<Rule>(sharpedRule);
                    qdpGraph.addNode(ruleNode);
                    if (ruleIterator.previousIndex() == 0) {
                        entryNodes.add(ruleNode);
                    } else {
                        qdpGraph.addEdge(lastRuleNode, ruleNode);
                    }
                    lastRuleNode = ruleNode;
                } else {
                    final ImmutableMap<INode, ImmutableSet<IEdge>> edgeSuccessors =
                        idpGraph.getSuccessors(edge.to);

                    for (final ImmutableSet<IEdge> succEdges : edgeSuccessors.values()) {
                        for (final IEdge succEdge : succEdges) {
                            if (succEdge.type.isInf()) {
                                Rule sharpedRule;
                                if (succEdge.fromPos.isEmptyPosition()) {
                                    sharpedRule = this.getSharpedRule(
                                        rule,
                                        sharpSymbolMap,
                                        ruleIterator.previousIndex() == 0,
                                        true);
                                } else {
                                    final TRSTerm newRight = rule.getRight().getSubterm(this.convertPosition(succEdge.fromPos));
                                    sharpedRule = Rule.create(
                                        this.getSharpedTerm(
                                            rule.getLeft(),
                                            sharpSymbolMap,
                                            ruleIterator.previousIndex() == 0),
                                        this.getSharpedTerm(
                                            newRight,
                                            sharpSymbolMap,
                                            true));
                                }

                                final Node<Rule> ruleNode = new Node<Rule>(sharpedRule);
                                qdpGraph.addNode(ruleNode);

                                nodeSucceccors.add(ruleNode, succEdge);

                                if (ruleIterator.previousIndex() == 0) {
                                    entryNodes.add(ruleNode);
                                } else {
                                    qdpGraph.addEdge(lastRuleNode, ruleNode);
                                }
                            }
                        }
                    }
                }
            }
        }
        return entryNodes;
    }

    private void linkQDPGraph(final Graph<Rule, ?> qdpGraph,
        final CollectionMap<Node<Rule>, IEdge> nodeSucceccors,
        final Map<IEdge, Set<Node<Rule>>> edgeEntryNodes) {
        for (final Map.Entry<Node<Rule>, Collection<IEdge>> nodeSucc : nodeSucceccors.entrySet()) {
            final Node<Rule> node = nodeSucc.getKey();
            for (final IEdge succEdge : nodeSucc.getValue()) {
                final Set<Node<Rule>> succNodes = edgeEntryNodes.get(succEdge);
                for (final Node<Rule> succNode : succNodes) {
                    qdpGraph.addEdge(node, succNode);
                }
            }
        }
    }

    private Rule getSharpedRule(final Rule rule,
            final Map<FunctionSymbol, FunctionSymbol> sharpSymbolMap,
            final boolean deepSharpLeft,
            final boolean deepSharpRight) {
        return Rule.create(
            this.getSharpedTerm(
                rule.getLeft(),
                sharpSymbolMap,
                deepSharpLeft),
            this.getSharpedTerm(
                rule.getRight(),
                sharpSymbolMap,
                deepSharpRight)
        );
    }

    private <T extends TRSTerm> T getSharpedTerm(final T term,
            final Map<FunctionSymbol, FunctionSymbol> sharpSymbolMap,
            final boolean deepSharp) {
        if (term.isVariable()) {
            return term;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) term;
            final FunctionSymbol sharpedRootSymbol = sharpSymbolMap.get(fa.getRootSymbol());
            assert sharpedRootSymbol != null : "use scc processor before this one";

            return this.uncheckedGetSharpedTerm(term, sharpSymbolMap, deepSharp);
        }
    }

    @SuppressWarnings("unchecked")
    private <T extends TRSTerm> T uncheckedGetSharpedTerm(final T term,
        final Map<FunctionSymbol, FunctionSymbol> sharpSymbolMap,
        final boolean deepSharp) {
        if (term.isVariable()) {
            return term;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) term;
            FunctionSymbol sharpedRootSymbol = sharpSymbolMap.get(fa.getRootSymbol());
            if (sharpedRootSymbol == null) {
                sharpedRootSymbol = fa.getRootSymbol();
            }
            if (deepSharp) {
                final ArrayList<TRSTerm> newArguments = new ArrayList<TRSTerm>(fa.getArguments().size());
                for (final TRSTerm arg : fa.getArguments()) {
                    newArguments.add(this.uncheckedGetSharpedTerm(arg, sharpSymbolMap, true));
                }

                return (T) TRSTerm.createFunctionApplication(sharpedRootSymbol, newArguments);
            } else {
                return (T) TRSTerm.createFunctionApplication(sharpedRootSymbol, fa.getArguments());
            }
        }
    }

    private List<List<Rule>> convertEdge(
        final IDPProblem idp,
        final aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap convertedPredefinedMap,
        final PredefinedFunctionsManagerNegPos npMan,
        final FreshNameGenerator freshNames,
        final Map<FunctionSymbol, FunctionSymbol> sharpSymbolMap,
        final Set<TRSFunctionApplication> qTerms,
        final IEdge edge,
        final Itpf condition) throws IntOutOfRangeException {
        final List<List<Rule>> result = new ArrayList<List<Rule>>();

        final IDependencyGraph idpGraph = idp.getIdpGraph();
        final IDPPredefinedMap predefinedMap = idpGraph.getPredefinedMap();

        clauses : for (final ItpfConjClause clause : condition.getClauses()) {
            final Set<Pair<ITerm<?>, ITerm<?>>> unificationTerms = new LinkedHashSet<Pair<ITerm<?>,ITerm<?>>>();
            final List<Pair<ITerm<?>, ITerm<?>>> rewriteConditions = new ArrayList<Pair<ITerm<?>,ITerm<?>>>();

            for (final Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                if (literal.getValue()) {
                    final ItpfAtom atom = literal.getKey();
                    if (atom.isItp()) {
                        final ItpfItp itp = (ItpfItp) atom;
                        if (itp.getRelation() == ItpRelation.EQ) {
                            unificationTerms.add(new Pair<ITerm<?>, ITerm<?>>(itp.getL(), itp.getR()));
                        }
                    }
                }
            }

            final Unification unify = new Unification(unificationTerms, predefinedMap);

            final ISubstitution mgu = unify.getMgu();
            if (mgu == null) {
                // clause is UNSAT
                continue clauses;
            }
            final PolyTermSubstitution polyTermMgu = TermToPolyTermSubstitution.create(mgu, predefinedMap, idpGraph.getPolyInterpretation());

            final ITerm<?> fromITerm = idpGraph.getTerm(edge.from).getSubterm(edge.fromPos).applySubstitution(mgu);
            final Set<IVariable<?>> fromITermVars = fromITerm.getVariables();
//            fromITerm = getQNormalFormArgsTem(fromITerm, idpGraph.getQ(), idpGraph.getFreshVarGenerator());

            final ITerm<?> toITerm;

            if (edge.from.equals(edge.to)) {
                toITerm = idpGraph.getTerm(edge.to).applySubstitution(idpGraph.getLoopRenaming(edge.from)).applySubstitution(mgu);
            } else {
                toITerm = idpGraph.getTerm(edge.to).applySubstitution(mgu);
            }
            final Set<IVariable<?>> toITermVars = toITerm.getVariables();

            if (fromITerm.equals(toITerm) && !edge.fromPos.isEmptyPosition()) {
                // matching edge
                continue clauses;
            }

            final LinkedHashSet<IVariable<?>> sharedVars = new LinkedHashSet<IVariable<?>>(fromITermVars);
            sharedVars.retainAll(toITermVars);
            for (final IVariable<?> sharedVar : sharedVars) {
                rewriteConditions.add(new Pair<ITerm<?>, ITerm<?>>(sharedVar, sharedVar));
            }

            for (final Entry<ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                if (literal.getValue()) {
                    final ItpfAtom atom = literal.getKey().applySubstitution(polyTermMgu);
                    if (atom.isItp()) {
                        final ItpfItp itp = ((ItpfItp) atom);
                        switch (itp.getRelation()) {
                        case EQ:
                            break;
                        case TO:
                        case TO_PLUS:
                        case TO_TRANS:
                            if (fromITermVars.containsAll(itp.getL().getVariables())
                                    && toITermVars.containsAll(itp.getR().getVariables())) {
                                rewriteConditions.add(new Pair<ITerm<?>, ITerm<?>>(itp.getL(), itp.getR()));
                            }
                            break;
                        default:
                            // drop condition
                            throw new UnsupportedOperationException("unknown condition");
                        }
                    } else if (atom.isPoly()) {
                        final ItpfPolyAtom<?> polyAtom = (ItpfPolyAtom<?>) atom;
                        final Polynomial<?> poly = polyAtom.getPoly();
                        if (fromITermVars.containsAll(polyAtom.getVariables())) {
                            IFunctionSymbol<?> sign;
                            ImmutableList<? extends SemiRingDomain<?>> domain;
                            if (poly.getRing().isSameRing(BigInt.ONE)) {
                                domain = DomainFactory.INTEGER_INTEGER;
                            } else {
                                throw new UnsupportedOperationException("unknown ring");
                            }
                            switch(polyAtom.getConstraintType()) {
                            case EQ:
                                sign = predefinedMap.getFunctionSymbol(Func.Eq, domain);
                                break;
                            case GE:
                                sign = predefinedMap.getFunctionSymbol(Func.Ge, domain);
                                break;
                            case GT:
                                sign = predefinedMap.getFunctionSymbol(Func.Gt, domain);
                                break;
                            default:
                                throw new UnsupportedOperationException("unknown relation");
                            }

                            final ITerm<?> zero = poly.getRing().zero().getTerm(predefinedMap);

                            final ITerm<?> polyTerm = polyAtom.getPoly().toTerm(idp.getPredefinedMap());
                            final IFunctionApplication<?> polyAtomTerm = IFunctionApplication.create(sign, polyTerm, zero);

                            rewriteConditions.add(new Pair<ITerm<?>, ITerm<?>>(polyAtomTerm, predefinedMap.getBooleanTrue().getTerm()));
                        } else {
                            final Pair<ITerm<?>, ITerm<?>> rewriteCond = IDP2toQDPProcessor.getPolyAtomCondition(polyAtom, fromITermVars, toITermVars, predefinedMap);
                            if (rewriteCond != null) {
                                rewriteConditions.add(rewriteCond);
                            }
                        }
                    }
                }
            }

            final ArrayList<TRSTerm> condArgsRight = new ArrayList<TRSTerm>();
            final ArrayList<TRSTerm> condArgsLeft = new ArrayList<TRSTerm>();

            final TRSTerm fromTerm = this.convertToQDPTerm(npMan, fromITerm);
            final Set<TRSVariable> fromTermVars = fromTerm.getVariables();
            final TRSTerm toTerm = this.convertToQDPTerm(npMan, toITerm);
            final Set<TRSVariable> toTermVars = toTerm.getVariables();

            for (final Pair<ITerm<?>, ITerm<?>> rewriteCond : rewriteConditions) {
                final TRSTerm newFrom = this.convertToQDPTerm(
                    npMan,
                    rewriteCond.x);
                final TRSTerm newTo = this.convertToQDPTerm(
                    npMan,
                    rewriteCond.y);
                if (!newFrom.equals(newTo)
                        && fromTermVars.containsAll(newFrom.getVariables())
                        && toTermVars.containsAll(newTo.getVariables())) {
                    condArgsRight.add(newFrom);
                    condArgsLeft.add(newTo);
                }
            }

            if (!fromTerm.isVariable()) {
                final ArrayList<TRSTerm> fromVariables = new ArrayList<TRSTerm>(fromTerm.getVariables());
                condArgsRight.addAll(fromVariables);
                condArgsLeft.addAll(fromVariables);
            } else {
                throw new UnsupportedOperationException("variable at root position not supported by QDP");
            }

            final FunctionSymbol condFs = FunctionSymbol.create(
                freshNames.getFreshName(
                    "cond_" + edge.from.id + "_" + edge.to.id,
                    false),
                    condArgsRight.size());

            final FunctionSymbol sharpCondFs = FunctionSymbol.create(
                freshNames.getFreshName(
                    condFs.getName().toUpperCase(),
                    false),
                    condArgsRight.size());

            this.addCondTermToQ(condFs, qTerms);

            sharpSymbolMap.put(condFs, sharpCondFs);

            final TRSFunctionApplication condRight = TRSTerm.createFunctionApplication(condFs, condArgsRight);
            final TRSFunctionApplication condLeft = TRSTerm.createFunctionApplication(condFs, condArgsLeft);

            final ArrayList<Rule> clauseRules = new ArrayList<Rule>();

            if (!condRight.equals(condLeft)) {
                final Rule ruleLeftToCondRight = Rule.create((TRSFunctionApplication) fromTerm, condRight);
                final Rule condLeftToRuleRight = Rule.create(condLeft, toTerm);

                clauseRules.add(ruleLeftToCondRight);
                clauseRules.add(condLeftToRuleRight);

                final Iterator<TRSFunctionApplication> qIterator = qTerms.iterator();
                final Set<TRSTerm> condLeftSubTerms = condLeft.getSubTerms();
                while (qIterator.hasNext()) {
                    final TRSFunctionApplication qTerm = qIterator.next();
                    for (final TRSTerm condLeftSubTerm : condLeftSubTerms) {
                        if (qTerm.matches(condLeftSubTerm)) {
                            qIterator.remove();
                            break;
                        }
                    }
                }
            } else {
                final Rule rule = Rule.create((TRSFunctionApplication) fromTerm, toTerm);
                clauseRules.add(rule);
            }

            result.add(clauseRules);
        }

        return result;
    }

    private void addCondTermToQ(final FunctionSymbol condFs,
        final Set<TRSFunctionApplication> qTerms) {
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(condFs.getArity());
        for (int i = 0; i < condFs.getArity(); i++) {
            args.add(TRSTerm.createVariable("x" + i));
        }

        qTerms.add(TRSTerm.createFunctionApplication(condFs, args));
    }

    private Map<FunctionSymbol, FunctionSymbol> createSharpSymbolMap(final IDependencyGraph idpGraph,
        final aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap convertedPredefinedMap,
        final PredefinedFunctionsManagerNegPos npMan,
        final FreshNameGenerator freshNames) {
        final Map<FunctionSymbol, FunctionSymbol> result = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        final LinkedHashSet<IFunctionSymbol<?>> symbolsToSharp = new LinkedHashSet<IFunctionSymbol<?>>(idpGraph.getDefinedSymbols());
        symbolsToSharp.addAll(CollectionUtil.getRootSymbols(idpGraph.getQ().getUserDefinedTerms()));

        for (final IFunctionSymbol<?> fs : symbolsToSharp) {
            final FunctionSymbol convertedFs = this.convertFunctionSymbol(fs);
            final FunctionSymbol sharpSymbol = FunctionSymbol.create(
                freshNames.getFreshName(convertedFs.getName().toUpperCase(), false),
                convertedFs.getArity());

            result.put(convertedFs, sharpSymbol);
        }

        for (final IFunctionSymbol<?> predefined : idpGraph.getPredefinedFunctions()) {
            if (!predefined.getSemantics().isConstructor()) {
                final FunctionSymbol predefinedFs = this.convertFunctionSymbol(predefined);

                final FunctionSymbol definedFs = npMan.substituteFunctionSymbol(predefinedFs);
                final FunctionSymbol sharpSymbol = FunctionSymbol.create(
                    freshNames.getFreshName(definedFs.getName().toUpperCase(), false),
                    predefinedFs.getArity());
                result.put(definedFs, sharpSymbol);
            }
        }

        return result;
    }

    private aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap convertPredefinedMap(final IDPProblem idp) {
        final Map<FunctionSymbol, PredefinedFunction<? extends Domain>> mapping = new LinkedHashMap<FunctionSymbol, PredefinedFunction<? extends Domain>>();

        final ImmutableSet<IFunctionSymbol<?>> usedFunctionSymbols = idp.getIdpGraph().getFunctionSymbols();
        final Set<String> usedFsNames = new LinkedHashSet<String>();
        for (final IFunctionSymbol<?> usedFs : usedFunctionSymbols) {
            usedFsNames.add(usedFs.getName());
        }

        for (final Entry<ImmutablePair<String, Integer>, aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction<?, ?>> mapEntry : idp.getPredefinedMap().getMapping().entrySet()) {
            final FunctionSymbol fs = FunctionSymbol.create(mapEntry.getKey().x, mapEntry.getKey().y);

            final PredefinedFunction<?> predefFunction = this.convertPredefinedFunction(mapEntry.getValue());

            mapping.put(fs, predefFunction);
        }

        final aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap newMap = new aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap(ImmutableCreator.create(mapping), usedFsNames);

        return newMap;
    }

    private PredefinedFunction<? extends Domain> convertPredefinedFunction(final aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction<?, ?> function) {
        final String funcName = function.getFunc().name();
        final PredefinedFunction.Func newFunc = Enum.valueOf(PredefinedFunction.Func.class, funcName);

        if (function.isArithmetic() || function.isBitwise()) {
            if (function.getArity() == 1) {
                return aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedSemanticsFactory.getFunction(newFunc, ImmutableCreator.create(java.util.Collections.singletonList(aprove.verification.dpframework.IDPProblem.PfFunctions.domains.DomainFactory.INTEGERS)));
            } else if (function.getArity() == 2) {
                return aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedSemanticsFactory.getFunction(newFunc, aprove.verification.dpframework.IDPProblem.PfFunctions.domains.DomainFactory.INTEGER_INTEGER);
            }
        } else if (function.isRelation()) {
            return aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedSemanticsFactory.getFunction(newFunc, aprove.verification.dpframework.IDPProblem.PfFunctions.domains.DomainFactory.INTEGER_INTEGER);
        } else if (function.isBoolean()) {
            if (function.getArity() == 1) {
                return aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedSemanticsFactory.getFunction(newFunc, ImmutableCreator.create(java.util.Collections.singletonList(aprove.verification.dpframework.IDPProblem.PfFunctions.domains.DomainFactory.BOOLEAN)));
            } else if (function.getArity() == 2) {
                return aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedSemanticsFactory.getFunction(newFunc, aprove.verification.dpframework.IDPProblem.PfFunctions.domains.DomainFactory.BOOLEAN_BOOLEAN);
            }
        }

        throw new UnsupportedOperationException("function can not be converted: " + function);
    }

    private TRSTerm convertToQDPTerm(final PredefinedFunctionsManagerNegPos pfFunctionManager, final ITerm<?> term) throws IntOutOfRangeException {
        final TRSTerm idpV1Term = this.convertToIDPv1Term(term);
        if (idpV1Term.isVariable()) {
            return idpV1Term;
        } else {
            return pfFunctionManager.extractTerm(idpV1Term);
        }
    }

    @SuppressWarnings("unchecked")
    private <T extends TRSTerm> Set<T> convertToIDPv1Term(final Collection<? extends ITerm<?>> terms) throws IntOutOfRangeException {
        final LinkedHashSet<T> result = new LinkedHashSet<T>();

        for (final ITerm<?> term : terms) {
            result.add((T) this.convertToIDPv1Term(term));
        }

        return result;
    }

    private Position convertPosition(final IPosition pos) {
        return Position.create(pos.toIntArray());
    }

    private TRSTerm convertToIDPv1Term(final ITerm<?> term) {
        if (term.isVariable()) {
            return TRSTerm.createVariable(((IVariable<?>) term).getName());
        } else {
            final IFunctionApplication<?> ifa = (IFunctionApplication<?>) term;

            final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(ifa.getArguments().size());
            for (final ITerm<?> argTerm : ifa.getArguments()) {
                args.add(this.convertToIDPv1Term(argTerm));
            }

            final FunctionSymbol rootFs = this.convertFunctionSymbol(ifa.getRootSymbol());

            return TRSTerm.createFunctionApplication(rootFs, args);
        }
    }

    private Set<FunctionSymbol> convertFunctionSymbol(final Collection<IFunctionSymbol<?>> fss) {
        final LinkedHashSet<FunctionSymbol> result = new LinkedHashSet<FunctionSymbol>();

        for (final IFunctionSymbol<?> fs : fss) {
            result.add(this.convertFunctionSymbol(fs));
        }

        return result;
    }

    private FunctionSymbol convertFunctionSymbol(final IFunctionSymbol<?> rootSymbol) {
        return FunctionSymbol.create(rootSymbol.getName(), rootSymbol.getArity());
    }

    /**
     * creates QTerms for QDPProblem
     */
    private Set<TRSFunctionApplication> createQdpQTerms(final Set<TRSFunctionApplication> explicitOrigQTerms,
        final PredefinedFunctionsManagerNegPos npMan) throws IntOutOfRangeException {
        // build Q
        final Set<TRSFunctionApplication> qTerms =
            new LinkedHashSet<TRSFunctionApplication>(explicitOrigQTerms.size());

        // postprocess those qTerms by npMan, too
        for (final TRSFunctionApplication origQTerm : explicitOrigQTerms) {
            final TRSFunctionApplication newQTerm = npMan.extractTerm(origQTerm);
            qTerms.add(newQTerm);
        }
        return qTerms;
    }

    public class IDPtoQDPProof extends DefaultProof implements DOT_Able {

        private final QDPProblem qdp;

        public IDPtoQDPProof(final QDPProblem qdp) {
            this.qdp = qdp;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Represented integers and predefined function symbols by Terms";
        }

        @Override
        public String toDOT() {
            return this.qdp.getDependencyGraph().toDOT();
        }
    }

    public static class Arguments {
        // when do we want to be applicable?
        public ToTermApplicability apply = ToTermApplicability.ALWAYS;

        // max absolute value of integer literal accepted for conversion
        public int limit = 1023;
    }

}
