/*
 * Created on 16.04.2005
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;

/**
 * @author thiemann
 */
public abstract class QDPTransformationProcessor extends QDPProblemProcessor {

    private final QDPTransformation transformation;
    private final int limit;

    public QDPTransformationProcessor(final QDPTransformation transformation,
            final Arguments arguments) {
        this.transformation = transformation;
        this.limit = arguments.limit;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return qdp.getDependencyGraph().isSCC();
    }


    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        final QDependencyGraph graph = qdp.getDependencyGraph();
        final Graph<Rule,?> gr = graph.getGraph();

        final QTransformationInfo transInfo = graph.getTransformationInfo();
        final int originSize = transInfo.getNrOfOrigins();
        final int Psize = qdp.getP().size();

        for (final Node<Rule> s_to_t : gr.getNodes()) {
            final AbortableIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>> resultIter =
                this.getTransformedRules(s_to_t, gr, qdp, aborter);
            nextExample: while (resultIter.hasNext(aborter)) {
                final Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>> result =
                    resultIter.next(aborter);

                // okay, we are successful.
                // let us replace s_to_t by the new Rules

                final Set<Pair<Rule, Rule>> newRules = result.y;
                final Triple<Position, Set<Rule>, Rule> triple = result.z;
                Position p;
                Set<Rule> usable;
                Rule rewriteRule;
                if (triple == null) {
                    p = null;
                    usable = null;
                    rewriteRule = null;
                } else {
                    p = triple.x;
                    usable = triple.y;
                    rewriteRule = triple.z;
                }

                final Set<Rule> onlyResultingRules = new LinkedHashSet<>();
                for (final Pair<Rule, Rule> pair : newRules) {
                    onlyResultingRules.add(pair.y);
                }

                final Pair<QDPProblem, Integer> newQdpCounter =
                    qdp.getTransformedProblem(this.transformation, s_to_t, onlyResultingRules, p);
                final QDPProblem newQdp = newQdpCounter.x;

                // let us check heuristics
                final int count = newQdpCounter.y;


                // first check nr of transformations allowed for for this dp
                if (count > this.limit) {

                    // if this is not yet safe, try size criterion
                    final QDependencyGraph newGraph = newQdp.getDependencyGraph();
                    final Set<Node<Rule>> newSccNodes = newGraph.getNodesOnSCCs();
                    if (newSccNodes.size() >= Psize) {
                        // and finally check origin criterion
                        QTransformationInfo newTransformation = newGraph.getTransformationInfo();
                        newTransformation = newTransformation.getSubInfo(newSccNodes);
                        if (originSize == newTransformation.getNrOfOrigins()) {
                            if (result.w == null || !result.w.safeTransformation()) {
                                aborter.checkAbortion();
                                continue nextExample;
                            }
                        }
                    }
                }

                final Proof proof = new TransformationProof(qdp, newQdp, s_to_t.getObject(), this.transformation, newRules, p, usable, rewriteRule);
                return ResultFactory.proved(newQdp, result.x, proof);
            }
        }

        return ResultFactory.unsuccessful();
    }


    /**
     * the transformationHeuristic can be returned optional to make some additional transformations safe.
     * @param s_to_t
     * @param gr
     * @param qdp
     * @param aborter
     * @return
     * @throws AbortionException
     */
    protected abstract AbortableIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>> getTransformedRules(Node<Rule> s_to_t,
        Graph<Rule, ?> gr,
        QDPProblem qdp,
        Abortion aborter) throws AbortionException;

    /**
     * the transformationHeuristic can be used to make some additional transformations safe.
     */
    static interface TransformationHeuristic {

        public boolean safeTransformation();

    }



    /**
     * an iterator that one time delivers the given element, if
     * this is not null. For null nothing is returned.
     * @author thiemann
     *
     * @param <U>
     */
    static class MaybeOneIterator<U> implements AbortableIterator<U> {

        private U element;

        public MaybeOneIterator(final U element) {
            this.element = element;
        }

        @Override
        public boolean hasNext(final Abortion aborter) {
            return this.element != null;
        }

        @Override
        public U next(final Abortion aborter) {
            if (this.element != null) {
                final U e = this.element;
                this.element = null;
                return e;
            } else {
                throw new NoSuchElementException();
            }
        }

    }

    public static final AbortableIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>> EMPTY_ITERATOR =
        new MaybeOneIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>>(
            null);

    static class TransformationProof extends QDPProof {

        private final Rule s_to_t;
        /**
         * This set contains pairs, where the first element is the generated rule and the second element is a
         * possibly renamed variant that already existed in the QDP.
         */
        private final Set<Pair<Rule, Rule>> newDPs;
        private final QDPTransformation transformation;
        private final Position position;
        private final Set<Rule> usableRules;
        private final Rule rewriteRule;
        private final QDPProblem origQDP;
        private final QDPProblem newQDP;

        private TransformationProof(final QDPProblem origQDP, final QDPProblem newQDP, final Rule s_to_t,
                final QDPTransformation transformation, final Set<Pair<Rule, Rule>> newDPs, final Position position,
                final Set<Rule> usableRules, final Rule rewriteRule) {
            this.s_to_t = s_to_t;
            this.newDPs = newDPs;
            this.transformation = transformation;
            this.position = position;
            this.usableRules = usableRules;
            this.rewriteRule = rewriteRule;
            this.origQDP = origQDP;
            this.newQDP = newQDP;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuffer s = new StringBuffer();
            s.append(o.export("By "+this.transformation.getPredicate()+" "+o.cite(this.transformation.getCitation())+" the rule ")+o.math(o.export(this.s_to_t))+
                    (this.position == null ? "" : " at position "+o.export(this.position))+" we obtained the following new rules " + o.cite(Citation.LPAR04) + ":");
            s.append(o.cond_linebreak());
            s.append(o.set(this.newDPs, Export_Util.RULES));
            s.append(o.cond_linebreak());
            return s.toString();
        }


        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            final Element rule = this.s_to_t.toCPF(doc, xmlMetaData);
            final Element position = this.position == null ? null : this.position.toCPF(doc, xmlMetaData);
            Element usableRules = null;
            if (this.usableRules != null) {
                usableRules = CPFTag.USABLE_RULES.create(doc,
                        CPFTag.rules(doc, xmlMetaData, this.usableRules));
            }
            final Set<Rule> resultingPairs = new LinkedHashSet<Rule>();
            for (final Pair<Rule, Rule> p : this.newDPs) {
                resultingPairs.add(p.y);
            }
            final Element newPairsElement = CPFTag.rules(doc, xmlMetaData, resultingPairs);

            Element e = null;
                switch (this.transformation) {
                case ForwardInstantiation:
                case Instantiation:
                    if (modus.isPositive()) {
                        final Element instantiations = CPFTag.INSTANTIATIONS.create(doc, newPairsElement);
                        if (this.transformation == QDPTransformation.Instantiation) {
                            e = CPFTag.INSTANTIATION_PROC.create(doc, rule, instantiations);
                        } else {
                            e = CPFTag.FORWARD_INSTANTIATION_PROC.create(doc, rule, instantiations);
                            if (usableRules != null) {
                                e.appendChild(usableRules);
                            }
                        }
                    } else {
                        e = CPFTag.INSTANTIATION_PROC.create(doc,
                                CPFTag.dps(doc, xmlMetaData, this.newQDP.getP()));
                    }
                    break;
                case Narrowing:
                    e = CPFTag.NARROWING_PROC.create(doc, rule, position,
                            CPFTag.NARROWINGS.create(doc, newPairsElement));
                    break;
                case Rewriting:
                    final Pair<Rule,Rule> generatedResulting = this.newDPs.iterator().next();
                    e = CPFTag.REWRITING_PROC.create(doc,
                            rule,
                            CPFTag.REWRITE_STEP.create(doc,
                                    position,
                                    this.rewriteRule.toCPF(doc, xmlMetaData),
                                    generatedResulting.x.getRight().toCPF(doc, xmlMetaData)),
                            generatedResulting.y.toCPF(doc, xmlMetaData),
                            usableRules
                            );
                    break;
            }
            e.appendChild(childrenProofs[0]);

            return (modus.isPositive() ? CPFTag.DP_PROOF : CPFTag.DP_NONTERMINATION_PROOF).create(doc, e);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }

    /**
     * For use with our children and annotation @ParamsViaArgumentObjects
     */
    public static class Arguments {
        public int limit = 0;
    }

}
