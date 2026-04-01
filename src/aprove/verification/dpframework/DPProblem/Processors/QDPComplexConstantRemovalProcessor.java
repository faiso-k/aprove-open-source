package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;
import immutables.*;

/**
 * Remove complex terms without variables by introducing new variables.
 * F(x) -> G(x, le(x, s(s(s(s(0))))))
 * G(x, y) -> F(x)
 *
 * becomes
 *
 * F(x, x_removed) -> G(x, le(x, x_removed), x_removed)
 * G(x, y, x_removed) -> F(x, x_removed)
 * @author cotto
 */
@NoParams
public class QDPComplexConstantRemovalProcessor extends QDPProblemProcessor {

    @Override
    public boolean isQDPApplicable(final QDPProblem qdpParam) {
        return qdpParam.getMinimal() && qdpParam.getInnermost();
    }

    /**
     * Clean up the given QDP.
     * @param qdpParam The QDP to analyze.
     * @param aborter Not used.
     * @throws AbortionException Not used.
     * @return The new QDP with a proof, if successful.
     */
    @Override
    public Result processQDPProblem(
            final QDPProblem qdpParam,
            final Abortion aborter)
            throws AbortionException {
        assert (qdpParam != null);
        return new Calculator(qdpParam, aborter).processQDPProblem();
    }

    /**
     * The real calculator for the fixed QDP.
     */
    private static class Calculator {
        /**
         * The QDP to work with.
         */
        private final QDPProblem qdp;

        /**
         * The aborter is used to stop the check for non-overlappingness if
         * needed.
         */
        private final Abortion aborter;

        /**
         * The qUsableRules are used to find out which rules must be
         * non-overlapping.
         */
        private final QUsableRules qUsableRules;

        /**
         * Just a dummy used to generate a fake rule in order to find the usable
         * rules for a specific term.
         */
        private final TRSFunctionApplication dummyLhs;

        /**
         * This set contains all function symbols that may not be used for tuple
         * symbols with arity+1 (with additional variable). Some function symbol
         * is in this forbidden set if it is used in R or Q or it is a newly
         * created function symbol (used createFreshFs()).
         */
        private final Set<FunctionSymbol> forbidden;

        /**
         * The head symbols of the DP-problem.
         */
        private final Set<FunctionSymbol> headSyms;

        /**
         * Remember the created fresh function symbols (so the result of
         * createFreshFs is always the same for the same set of parameters).
         */
        private final Map<Pair<String, Integer>, FunctionSymbol> created;

        /**
         * Create the real calculator for the given QDP.
         * @param qdpParam The QDP to clean.
         * @param aborterParam The aborter is used to stop the check for non-
         * overlappingness if needed.
         */
        public Calculator(
                final QDPProblem qdpParam, final Abortion aborterParam) {
            this.aborter = aborterParam;
            this.qUsableRules = qdpParam.getQUsableRulesCalculator();
            this.forbidden =
                new LinkedHashSet<>(qdpParam.getSignature());
            this.headSyms = qdpParam.getHeadSymbols();

            // initially every function symbols but a head symbol are forbidden
            // as fresh function symbols (because they already exist).
            this.forbidden.removeAll(this.headSyms);

            this.created =
                new LinkedHashMap<>();

            // create a dummy lhs which is definitely in Q-normal form
            // (here we take the term F(x,x,x,x,x) for some head-symbol F.
            final Iterator<FunctionSymbol> headIt = this.headSyms.iterator();
            if (!headIt.hasNext()) {
                this.qdp = null;
                this.dummyLhs = null;
            } else {
                this.qdp = qdpParam;
                final FunctionSymbol dummySymbol =
                    headIt.next();
                final int n = dummySymbol.getArity();
                final TRSVariable x = TRSTerm.createVariable("x");
                final ArrayList<TRSTerm> dummyArgs = new ArrayList<>(n);
                for (int i = 0; i < n; i++) {
                    dummyArgs.add(x);
                }
                this.dummyLhs = TRSTerm.createFunctionApplication(
                        dummySymbol, ImmutableCreator.create(dummyArgs));
            }
        }

        /**
         * Clean up the given QDP.
         * @throws AbortionException Not used.
         * @return The new QDP with a proof, if successful.
         */
        private Result processQDPProblem()
                throws AbortionException {
            if (this.qdp == null) {
                return ResultFactory.unsuccessful();
            }
            for (final Rule pair : this.qdp.getP()) {
                if (!this.headSyms.contains(pair.getRootSymbol())) {
                    return ResultFactory.unsuccessful();
                }
                final TRSTerm t = pair.getRight();
                if (t.isVariable() || !this.headSyms.contains(
                        ((TRSFunctionApplication) t).getRootSymbol())) {
                    return ResultFactory.unsuccessful();
                }
            }

            // find all candidates
            final Collection<Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>>>
                candidates = this.getComplexConstants();

            // find the best candidate for removal
            final Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>> selected =
                this.select(candidates);

            // remove the selected candidate
            final Triple<QDPProblem, TRSVariable, Map<Rule, Rule>> triple = this.remove(selected);

            if (triple != null) {
                final QDPProof proof = new RemovalProof(selected, triple.y, triple.z, this.qdp, triple.x);
                return ResultFactory.proved(
                        triple.x, YNMImplication.SOUND, proof);
            } else {
                return ResultFactory.unsuccessful();
            }
        }

        /**
         * Remove the given term and replace it with a fresh variable.
         * Additionally alter the QDP by adding this fresh variable to every
         * rule of the P (on both sides).
         * @param selected Information about the term to be removed.
         * @return The new QDPProblem, the fresh variable, and the map from old pairs to new pairs
         */
        private Triple<QDPProblem, TRSVariable, Map<Rule,Rule>> remove(
                final Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>> selected
                ) {
            if (selected != null) {
                // create a fresh variable
                final Set<TRSVariable> varSet = new LinkedHashSet<>();
                for (final Rule rule : this.qdp.getP()) {
                    varSet.addAll(rule.getVariables());
                }
                TRSVariable newVar = TRSTerm.createVariable("x_removed");
                int counter = 0;
                while (varSet.contains(newVar)) {
                    newVar = TRSTerm.createVariable("x_removed" + counter);
                    counter++;
                }

                // do the work
                final Set<Rule> newP = new LinkedHashSet<>();

                // remember the origin for every new rule
                final Map<Rule, Rule> ruleMap = new LinkedHashMap<>();

                for (final Rule rule : this.qdp.getP()) {
                    // 1) add the fresh variable to the left side of the DP rule
                    final ImmutableList<? extends TRSTerm> leftArgs = rule.getLeft().getArguments();
                    final ArrayList<TRSTerm> leftArgsNew = new ArrayList<>(leftArgs);
                    leftArgsNew.add(newVar);
                    final FunctionSymbol leftFs = rule.getLeft().getRootSymbol();
                    // do _not_ only take the old name with the new arity,
                    // because this might result in some symbol that already
                    // exists in R or Q.
                    final FunctionSymbol leftFsNew =
                        this.createFreshFs(leftFs.getName(), leftFs.getArity() + 1);
                    final TRSFunctionApplication newLeft =
                        TRSTerm.createFunctionApplication(leftFsNew, ImmutableCreator.create(leftArgsNew));
                    // 2) replace the term with the fresh variable (if the term
                    // occurs in this rule)
                    TRSTerm right = rule.getRight();
                    final Set<Position> positions = selected.x.get(rule);
                    if (positions != null) {
                        for (final Position pos : positions) {
                            right = right.replaceAt(pos, newVar);
                        }
                    }
                    // 3) add the fresh variable to the right side of the DP
                    // rule
                    final TRSFunctionApplication rhs = (TRSFunctionApplication) right;
                    final ImmutableList<? extends TRSTerm> rightArgs = rhs.getArguments();
                    final ArrayList<TRSTerm> rightArgsNew =
                        new ArrayList<>(rightArgs.size() + 1);
                    rightArgsNew.addAll(rightArgs);
                    rightArgsNew.add(newVar);
                    final FunctionSymbol rightFs = rhs.getRootSymbol();
                    // do _not_ only take the old name with the new arity,
                    // because this might result in some symbol that already
                    // exists in R or Q.
                    final FunctionSymbol rightFsNew = this.createFreshFs(rightFs.getName(), rightFs.getArity() + 1);
                    final TRSTerm newRight =
                        TRSTerm.createFunctionApplication(rightFsNew, ImmutableCreator.create(rightArgsNew));
                    final Rule newRule = Rule.create(newLeft, newRight);
                    ruleMap.put(rule, newRule);
                    newP.add(newRule);
                }
                final QDPProblem newQDP = this.constructQDP(newP, ruleMap);
                return new Triple<>(
                        newQDP,
                        newVar,
                        ruleMap);
            } else {
                return null;
            }
        }

        /**
         * Find a name for the function symbol so that the new function symbols
         * is not part of R or Q by adding ' to the name where needed.
         * @param name The name of the new function symbol.
         * @param arity The arity of the new function symbol.
         * @return A new function symbol which is not part of R or Q.
         */
        private FunctionSymbol createFreshFs(
                final String name,
                final int arity) {
            final Pair<String, Integer> pair = new Pair<>(name, arity);
            if (this.created.containsKey(pair)) {
                return this.created.get(pair);
            }

            String newName = name;
            FunctionSymbol candidate = FunctionSymbol.create(newName, arity);

            // forbidden: function symbol already used in R or Q _or_ already
            // created using this function (for some other name/arity pair).
            while (this.forbidden.contains(candidate)) {
                newName = newName + "'";
                candidate = FunctionSymbol.create(newName, arity);
            }
            this.created.put(pair, candidate);
            this.forbidden.add(candidate);
            return candidate;
        }

        /**
         * Build the new QDP Problem based on the information given by the new
         * rules (with added variable and removed term) and a map that gives
         * information about the origin for each new pair.
         * @param newP The new pairs.
         * @param ruleMap A map that gives the original pair for each new pair.
         * @return A QDPProblem based on the new pairs.
         */
        private QDPProblem constructQDP(final Set<Rule> newP,
                final Map<Rule, Rule> ruleMap) {
            final QDependencyGraph graph = this.qdp.getDependencyGraph();

            final Map<Node<Rule>, Node<Rule>> oldDpToNewDPs =
                new HashMap<>(this.qdp.getP().size());

            final Graph<Rule, ?> newPGraph = new Graph<>();

            for (final Node<Rule> dp : graph.getGraph().getNodes()) {
                final Rule rule = dp.getObject();
                final Rule newRule = ruleMap.get(rule);
                oldDpToNewDPs.put(dp, new Node<>(newRule));
            }
            // afterwards create edges
            for (final Edge<?, Rule> edge : graph.getGraph().getEdges()) {
                final Node<Rule> start = oldDpToNewDPs.get(edge.getStartNode());
                final Node<Rule> end = oldDpToNewDPs.get(edge.getEndNode());
                newPGraph.addEdge(start, end);
            }

            final QDPProblem newQDP = QDPProblem.create(
                    newPGraph, this.qdp.getRwithQ(), this.qdp.getMinimal());
            return newQDP;
        }

        /**
         * Find the best candidate, where the highest depth of the term is the
         * criteria.
         * @param candidates The collection containing all candidates.
         * @return The candidate with highest depth.
         */
        private Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>> select(
                final Collection<Triple<Map<Rule, Set<Position>>,
                    TRSTerm, Set<Rule>>> candidates) {
            int maxDepth = 1; // only ground terms with depth >1 are of interest
            Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>> max = null;
            for (final Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>> candidate
                    : candidates) {
                final TRSFunctionApplication fa = (TRSFunctionApplication) candidate.y;
                final int depth = candidate.y.getDepth();

                // also remove terms that call some (complicated?) rule,
                // although the term's depth is very small.
                // e.g. the constant "one_billion" where one_billion is defined
                // by some rules.
                if (this.qdp.getRwithQ().getDefinedSymbolsOfR().contains(
                        fa.getRootSymbol()) || depth > maxDepth) {
                    max = candidate;
                    maxDepth = depth;
                }
            }
            return max;
        }

        /**
         * Iterate over all DP rules and find the candidates.
         * @return All candidates with additional information about their origin
         * and position.
         * @throws AbortionException Used for isOverlapping.
         */
        public Collection<Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>>>
            getComplexConstants() throws AbortionException {
            final Collection<Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>>>
              result = new LinkedHashSet<>();
            for (final Rule currentRule : this.qdp.getP()) {
                final TRSTerm right = currentRule.getRight();
                final Position position = Position.create();
                this.findCandidates(position, right, result);
            }
            return result;
        }

        /**
         * Fill the result set with candidates.
         * @param position The position of the candidate inside the DP rule's
         * right side.
         * @param term The term that should be checked for candidates.
         * @param result The set containing all candidates with the origin and
         * position.
         * @throws AbortionException Used for isOverlapping.
         */
        private void findCandidates(
                final Position position,
                final TRSTerm term,
                final Collection<Triple<Map<Rule, Set<Position>>,
                    TRSTerm, Set<Rule>>> result
                ) throws AbortionException {
            if (term instanceof TRSFunctionApplication) {
                final TRSFunctionApplication rightFa = (TRSFunctionApplication) term;
                final FunctionSymbol rightFs = rightFa.getRootSymbol();
                for (int pos = 0; pos < rightFs.getArity(); pos++) {
                    final TRSTerm subTerm = rightFa.getArgument(pos);
                    final Position newPosition = position.append(pos);
                    final Pair<Boolean, Set<Rule>> isCandidate =
                        this.isCandidate(subTerm);
                    if (isCandidate.x) {
                        final Map<Rule, Set<Position>> map = this.findOccurences(subTerm);
                        final Triple<Map<Rule, Set<Position>>,
                        TRSTerm, Set<Rule>> triple = new Triple<>(
                                map,
                                subTerm,
                                isCandidate.y
                        );
                        result.add(triple);
                    } else {
                        this.findCandidates(newPosition, subTerm, result);
                    }
                }
            }
        }

        /**
         * Find all occurences of the given term.
         * @param termToFind The term to find.
         * @return A map giving all positions where the term occurs per rule.
         */
        private Map<Rule, Set<Position>> findOccurences(final TRSTerm termToFind) {
            final Map<Rule, Set<Position>> result =
                new LinkedHashMap<>();
            for (final Rule rule : this.qdp.getP()) {
                final TRSTerm right = rule.getRight();
                for (final Position pos : right.getPositions()) {
                    final TRSTerm subTerm = right.getSubterm(pos);
                    if (subTerm.equals(termToFind)) {
                        if (result.containsKey(rule)) {
                            result.get(rule).add(pos);
                        } else {
                            final Set<Position> positions =
                                new LinkedHashSet<>();
                            positions.add(pos);
                            result.put(rule, positions);
                        }
                    }
                }
            }
            return result;
        }

        /**
         * @param term The term to check.
         * @return A pair. First component is true iff the term is a candidate
         * (so has no variable inside). The second components gives the rules
         * that are checked for non-overlappingness.
         * @throws AbortionException Used for isOverlapping.
         */
        private Pair<Boolean, Set<Rule>> isCandidate(
                final TRSTerm term)
            throws AbortionException {
            if (term.getVariables().size() == 0) {
                return this.isNonOverlapping(term);
            } else {
                return new Pair<>(false, null);
            }
        }

        /**
         * Find out whether the rules that define the symbols used in the given
         * term are overlapping.
         * @param term The term that will be removed.
         * @return A pair. The first component is true if the results used for
         * the to-be-removed term are overlapping. The second component gives
         * the rules that were checked for non-overlappingness.
         * @throws AbortionException Kicks in when finding critical pairs takes
         * too long.
         */
        private Pair<Boolean, Set<Rule>> isNonOverlapping(
                final TRSTerm term)
            throws AbortionException {

            final Set<Rule> ruleSet =
                this.qUsableRules.getUsableRules(
                        Rule.create(this.dummyLhs, term));

            boolean nonOverlap;
            if (ruleSet.size() > 0) {
                nonOverlap =
                    !GeneralizedRule.getCriticalPairs(ruleSet).hasNext(this.aborter);
            } else {
                nonOverlap = true;
            }
            return new Pair<>(nonOverlap, ruleSet);
        }

    }

    /**
     * The proof shown when using this processor.
     */
    private static class RemovalProof extends QDPProof {
        /**
         * Information about the removed term.
         */
        private final Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>> selected;

        /**
         * The replacement variable.
         */
        private final TRSVariable newVar;

        /**
         * A map from old pairs to new pairs
         */
        private final Map<Rule,Rule> ruleMap;

        /**
         * the input DP-problem
         */
        private final QDPProblem origQDP;

        /**
         * the resulting DP-problem
         */
        private final QDPProblem newQDP;


        /**
         * Build the proof.
         * @param selectedParam Information about the removed term.
         * @param newVarParam The replacement variable.
         * @param rulemap the map from old to new pairs
         * @param origqdp the input DP-problem to this proc
         * @param newqdp the output DP-problem of this proc
         */
        public RemovalProof(
                final Triple<Map<Rule, Set<Position>>, TRSTerm, Set<Rule>>
                    selectedParam,
                final TRSVariable newVarParam,
            final Map<Rule, Rule> rulemap,
            final QDPProblem origqdp,
            final QDPProblem newqdp)
        {
            this.selected = selectedParam;
            this.newVar = newVarParam;
            this.ruleMap = rulemap;
            this.origQDP = origqdp;
            this.newQDP = newqdp;
        }

        /**
         * @param o The export util used to generate the proof.
         * @param level not used.
         * @return a string describing what this processor did.
         */
        @Override
        public String export(
                final Export_Util o,
                final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("In the following pairs the term without variables ");
            sb.append(o.export(this.selected.y));
            sb.append(" is replaced by the fresh variable ");
            sb.append(o.export(this.newVar));
            sb.append(".");
            sb.append(o.newline());
            for (final Map.Entry<Rule, Set<Position>> entry
                    : this.selected.x.entrySet()) {
                sb.append("Pair: ");
                sb.append(o.export(entry.getKey()));
                sb.append(o.newline());
                sb.append("Positions in right side of the pair: ");
                final int itemize = 3;
                sb.append(o.set(entry.getValue(), itemize));
            }
            if (this.selected.z.size() > 0) {
                sb.append("The following rules were checked for ");
                sb.append("non-overlappingness: ");
                final int rules = 4;
                sb.append(o.set(this.selected.z, rules));
            }
            sb.append("The new variable was added to all pairs as a new ");
            sb.append("argument");
            sb.append(o.cite(Citation.CONREM));
            sb.append(".");
            return sb.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (modus.isPositive()) {
                final Element m = CPFTag.RULE_MAP.create(doc);
                for (final Map.Entry<Rule, Rule> old_new : this.ruleMap.entrySet()) {
                    m.appendChild(CPFTag.RULE_MAP_ENTRY.create(doc, old_new.getKey().toCPF(doc, xmlMetaData), old_new
                        .getValue()
                        .toCPF(doc, xmlMetaData)));
                }
                return CPFTag.DP_PROOF.create(doc, CPFTag.COMPLEX_CONSTANT_REMOVAL_PROC.create(
                    doc,
                    this.selected.y.toCPF(doc, xmlMetaData),
                    m,
                    childrenProofs[0]));
            } else {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }

    }
}
