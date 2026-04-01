package aprove.verification.oldframework.Bytecode.Processors.ToIDPv1;

import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;
/**
 * In our FIGraph2ITRS conversion, we create one RuleCreator instance per
 * MethodGraph and use it to generate one rule per edge.
 *
 * @author Christian von Essen, Marc Brockschmidt
 */
public final class IDPv2ToIDPv1Utilities {
    /**
     * Do not use.
     */
    private IDPv2ToIDPv1Utilities() {
        assert (false) : "IDPv2ToIDPv1Utilities should not be instantiated";
    }

    /**
     * Given two terms of which one is possibly null, return either the non-null
     * term or the conjunction of both terms.
     *
     * @param l some term (or null)
     * @param r some term (or null, if <code>l</code> is not null)
     * @return some non-null value, either l, r or the conjunction of both.
     */
    public static TRSTerm getConjunction(final TRSTerm l, final TRSTerm r) {
        if (l == null) {
            return r;
        } else if (r == null) {
            return l;
        }
        return
            TRSTerm.createFunctionApplication(
                IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Land, DomainFactory.BOOLEAN),
                l,
                r
            );
    }

    /**
     * Given two terms of which one is possibly null, return either the non-null
     * term or the disjunction of both terms.
     *
     * @param l some term (or null)
     * @param r some term (or null, if <code>l</code> is not null)
     * @return some non-null value, either l, r or the conjunction of both.
     */
    public static TRSTerm getDisjunction(final TRSTerm l, final TRSTerm r) {
        if (l == null) {
            return r;
        } else if (r == null) {
            return l;
        }
        return TRSTerm.createFunctionApplication(
                IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Lor, DomainFactory.BOOLEAN),
                l, r);
    }

    /**
     * @param t some term (or null)
     * @return some term (probably the negated input)
     */
    public static TRSTerm negate(final TRSTerm t) {
        if (t == null) {
            return t;
        }
        return TRSTerm.createFunctionApplication(
                IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Lnot, DomainFactory.BOOLEAN),
                t);
    }

    /**
     * Transform a rule l -> r | c into a rule l' -> r | c' where
     * for all positions \pi with i = l|\pi \in \MdZ we have that
     * l'|\pi contains a new variable x and c' contains the term
     * x = i.
     *
     * This routine facilitates rule combination.
     *
     * @param rule Rule to shuffle matching from
     * @return A new rule
     */
    private static IGeneralizedRule shuffleMatchings(final IGeneralizedRule rule) {
        TRSFunctionApplication lhs = rule.getLeft();
        // Lets look if one of the sub-terms of the lhs is a number
        final Set <Position> matchingPositions = new LinkedHashSet<Position>();
        for (final Pair<Position, TRSTerm> pair : lhs.getPositionsWithSubTerms()) {
            final Position pi = pair.x;
            final TRSTerm t = pair.y;
            if (t instanceof TRSFunctionApplication
                && IDPPredefinedMap.DEFAULT_MAP.isPredefined(((TRSFunctionApplication) t).getRootSymbol())) {
                matchingPositions.add(pi);
            }
        }

        int variableIndex = 1;
        TRSTerm condition = rule.getCondTerm();
        for (final Position pi : matchingPositions) {
            final TRSVariable v = TRSTerm.createVariable("matching" + variableIndex++);
            final TRSTerm number = lhs.getSubterm(pi);
            lhs = (TRSFunctionApplication) lhs.replaceAt(pi, v);

            final TRSFunctionApplication matchingCondition =
                TRSTerm.createFunctionApplication(
                        IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER),
                        v, number);

            condition = IDPv2ToIDPv1Utilities.getConjunction(condition, matchingCondition);
        }

        return IGeneralizedRule.create(lhs, rule.getRight(), condition);
    }

    /**
     * @param iRule
     *            some iRule (i.e., IDPv2 stuff)
     * @return a corresponding IDPv1-based rule
     */
    public static IGeneralizedRule ruleToIDPv1(final IRule iRule) {
        return IGeneralizedRule.create(
                (TRSFunctionApplication) IDPv2ToIDPv1Utilities.termToIDPv1(iRule.getLeft()),
                IDPv2ToIDPv1Utilities.termToIDPv1(iRule.getRight()),
                IDPv2ToIDPv1Utilities.condToIDPv1(iRule.getCondition()));
    }

    /**
     * @param iTerm
     *            some iTerm (i.e., IDPv2 stuff)
     * @return a corresponding IDPv1-based term
     */
    private static TRSTerm termToIDPv1(final ITerm<?> iTerm) {
        if (iTerm == null) {
            return null;
        }
        if (iTerm instanceof IVariable<?>) {
            final IVariable<?> iVar = (IVariable<?>) iTerm;
            return TRSTerm.createVariable(iVar.getName());
        }

        final IFunctionApplication<?> iFA = (IFunctionApplication<?>) iTerm;
        final IFunctionSymbol<?> iFS = iFA.getRootSymbol();
        final ImmutableArrayList<ITerm<?>> iArgs = iFA.getArguments();

        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(iArgs.size());
        for (final ITerm<?> iArg : iArgs) {
            args.add(IDPv2ToIDPv1Utilities.termToIDPv1(iArg));
        }

        final FunctionSymbol fS = FunctionSymbol.create(iFS.getName(),
                iFS.getArity());
        final TRSTerm term = TRSTerm.createFunctionApplication(fS, args);

        return term;
    }

    /**
     * @param iCondition
     *            some Itpf (i.e., IDPv2 stuff)
     * @return a corresponding IDPv1-based term
     */
    private static TRSTerm condToIDPv1(final Itpf iCondition) {
        if (iCondition == null || iCondition.getClauses().isEmpty()) {
            return null;
        }

        TRSTerm cond = null;
        for (final ItpfConjClause iConj : iCondition.getClauses()) {
            TRSTerm conj = null;
            for (final Entry<ItpfAtom, Boolean> iLiteral : iConj.getLiterals()
                    .entrySet()) {
                final ItpfAtom iAtom = iLiteral.getKey();
                final boolean iAmNotNegated = iLiteral.getValue();
                if (iAtom instanceof ItpfItp) {
                    final ItpfItp iItp = (ItpfItp) iAtom;
                    assert (aprove.verification.idpframework.Core.PredefinedFunctions.IDPPredefinedMap.isBooleanTrue(iItp.getR())) : "Dunno what to do here, ask Martin";
                    assert (iItp.canIgnoreContextL() && iItp
                            .canIgnoreContextR()) : "Dunno what to do here, ask Martin";
                    final ITerm<?> iHaveNoNameForYou = iItp.getL();
                    final TRSTerm atom = IDPv2ToIDPv1Utilities.termToIDPv1(iHaveNoNameForYou);
                    final TRSTerm literal;
                    if (!iAmNotNegated) {
                        literal = aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.IDPv2ToIDPv1Utilities
                                .negate(atom);
                    } else {
                        literal = atom;
                    }
                    conj = aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.IDPv2ToIDPv1Utilities
                            .getConjunction(conj, literal);
                } else {
                    throw new NotYetImplementedException();
                }
            }
            cond = aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.IDPv2ToIDPv1Utilities
                    .getDisjunction(cond, conj);
        }

        return cond;
    }

    /**
     * @param aborter some aborter
     * @param ruleCreator an instance handling the actual conversion to rules.
     * @param edges the set of edges to encode
     * @param encodeMethodEnds
     *            if true, method calls will be properly encoded, i.e., we have
     *            rules of the form f(x,y) -> f(g(x),y) and f(g_end(z), y) ->
     *            h(z, y). If false, we will not try to use the information from
     *            the method return and generate rules f(x,y) -> g(x) and f(x,y)
     *            -> h(z, y).
     * @return set of rules corresponding to the input edges
     * @throws AbortionException happens when we are asked to stop.
     */
    public static Set<IGeneralizedRule> convertEdgesToIDPv1(
            Abortion aborter, final RuleCreator ruleCreator,
            final boolean forComplexity,
            final SCCAnnotations sccAnnotations,
            final TransformationDispatcher dispatcher,
            final Collection<Edge> edges,
            final boolean encodeMethodEnds) throws AbortionException {
        final Set<IGeneralizedRule> res = new LinkedHashSet<IGeneralizedRule>();
        final Set<IGeneralizedRule> skipRules = new LinkedHashSet<IGeneralizedRule>();
        for (final Edge edge : edges) {
            aborter.checkAbortion();

            //Do not encode the edge to an empty box.
            if (edge.getEnd().getState().callStackEmpty()) {
                continue;
            }

            final Collection<IRule> generatedRules = ruleCreator.convert(edge, forComplexity, encodeMethodEnds);

            for (final IRule genRule : generatedRules) {
                final IGeneralizedRule shuffledRule = IDPv2ToIDPv1Utilities.shuffleMatchings(IDPv2ToIDPv1Utilities.ruleToIDPv1(genRule));
                if (edge.getLabel() instanceof MethodSkipEdge) {
                    skipRules.add(shuffledRule);
                }
                res.add(shuffledRule);
            }
        }

        final MarkerFieldAnalysis markerAnalysis = (MarkerFieldAnalysis)
                sccAnnotations.getAnalysis(MarkerFieldAnalysis.class);

        if (markerAnalysis != null) {
            for (IGeneralizedRule skipRule : skipRules) {
                aborter.checkAbortion();

                TRSTerm newCond = null;
                for (final Entry<FieldRelation, AbstractVariableReference> e : markerAnalysis.getMarkerVarNames().entrySet()) {
                    final AbstractVariableReference countRef = e.getValue();
                    final FieldRelation fieldRel = e.getKey();
                    if (!markerAnalysis.wasEverIncreased(fieldRel)) {
                        //Get the variable:
                        final IVariable<BigInt> countTermVarOld =
                                dispatcher.getVariableLengthChanged(countRef, null);
                        final IVariable<BigInt> countTermVarNew =
                                dispatcher.getVariable(countRef, Collections.<AbstractVariableReference>emptySet(), null);

                        final IFunctionSymbol<BooleanRing> ge =
                                aprove.verification.idpframework.Core.PredefinedFunctions.IDPPredefinedMap.DEFAULT_MAP.<BooleanRing> getFunctionSymbolChecked(
                                        aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.Func.Ge,
                                        aprove.verification.idpframework.Core.PredefinedFunctions.Domains.DomainFactory.INTEGER_INTEGER);
                        final TRSTerm newAtom =
                                IDPv2ToIDPv1Utilities.termToIDPv1(
                                        ITerm.createFunctionApplication(
                                                ge,
                                                countTermVarOld,
                                                countTermVarNew));
                        newCond = IDPv2ToIDPv1Utilities.getConjunction(newCond, newAtom);
                    }
                }

                res.remove(skipRule);
                skipRule =
                        IGeneralizedRule.create(
                                skipRule.getLeft(),
                                skipRule.getRight(),
                                IDPv2ToIDPv1Utilities.getConjunction(skipRule.getCondTerm(), newCond));
                res.add(skipRule);
            }
        }
        return res;
    }
}
