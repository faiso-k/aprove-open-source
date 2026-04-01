package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.Globals.AproveVersion;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.QApplicativeUsableRules.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Heuristics.ReductionPair.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

public class QDPReductionPairProcessor extends QDPProblemProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPReductionPairProcessor");

    private final SolverFactory factory;
    private final boolean usable;
    private final boolean active;
    private final boolean allstrict;
    private final boolean aTrans;
    private final boolean mergeMutual;
    private final boolean scnpAsSizeChange;
    private final ReductionPairHeuristic heuristic;

    @ParamsViaArgumentObject
    public QDPReductionPairProcessor(final Arguments arguments) {
        this.active = arguments.active;
        this.allstrict = arguments.allstrict;
        this.aTrans = arguments.aTrans;
        this.factory = arguments.order;
        this.mergeMutual = arguments.mergeMutual;
        this.usable = arguments.usable;
        this.scnpAsSizeChange = arguments.scnpAsSizeChange;
        this.heuristic = arguments.heuristic;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return true;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem origqdp, final Abortion aborter) throws AbortionException {
        // is it allowed to restrict to usable rules?
        final boolean useUsable = this.usable && (origqdp.getInnermost() || origqdp.getMinimal());
        boolean useActive = this.active && useUsable;

        Set<Rule> usableRules = useUsable ? origqdp.getUsableRules() : origqdp.getR();
        Set<Rule> P = origqdp.getP();
        boolean allstrict = this.allstrict;

        // Run the given heuristic
        Set<Rule> searchSubset = this.heuristic.getSubset(origqdp);
        if (searchSubset == null || searchSubset.isEmpty()) {
            return ResultFactory.unsuccessful();
        }
        Set<Rule> notsearchSubset = new LinkedHashSet<Rule>(P);
        notsearchSubset.removeAll(searchSubset);

        final QActiveSolver solver = this.factory.getQActiveSolver();
        Pair<Map<Rule,Rule>,Map<Rule,Rule>> atransRes = null;

        // Currently a-transformation is not supported by either CoLoR or A3PAT.
        if (this.aTrans && !(Options.certifier.isRainbow() || Options.certifier.isA3pat() || Options.certifier.isCeta())) {
            final QApplicativeUsableRules qaur = origqdp.getApplicativeInfo();
            if (qaur != null) {
                // at this point R and Q are applicative
                if (QApplicativeUsableRules.applicativeRules(P)) {
                    aborter.checkAbortion();
                    // everything is applicative
                    boolean tryNonactive = true;
                    if (useActive && notsearchSubset.size() == 0) {
                        if (solver instanceof ImprovedQActiveSolver && ((ImprovedQActiveSolver)solver).improvedSolvingSupported()) {
                            tryNonactive = false;
                            // if we fail below, then there is no hope to make it without active
                            Quadruple<Map<Rule,Pair<TRSTerm, TRSTerm>>, Map<Rule, Pair<GeneralizedRule,Variable<AfsProp>>>, Formula<AfsProp>, Boolean> res;
                            res = qaur.getDPConstraints(P, origqdp.getHeadSymbols());
                            aborter.checkAbortion();
                            if (res != null) {
                                // lets try it, so prepapre input for Improved solver
                                final ImprovedQActiveSolver isolver = (ImprovedQActiveSolver) solver;

                                // P-component
                                final Set<Pair<TRSTerm,TRSTerm>> aP = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>(res.w.size());
                                for (final Pair<TRSTerm,TRSTerm> adp : res.w.values()) {
                                    aP.add(adp);
                                }
                                if (!allstrict && aP.size() == 1) {
                                    allstrict = true;
                                }

                                // active usable-rules
                                // we do not use a map, as it may be the case that variables are shared,
                                // and may also be the case that different original rules with different variables
                                // result in the same a-transed rule
                                final Collection<Pair<? extends GeneralizedRule,Variable<AfsProp>>> rules = new ArrayList<Pair<? extends GeneralizedRule,Variable<AfsProp>>>(res.x.size());
                                rules.addAll(res.x.values());

                                aborter.checkAbortion();
                                Pair<? extends ExportableOrder<TRSTerm>, Set<Variable<AfsProp>>> solverResult;
                                solverResult = isolver.solve(aP, rules, res.y, allstrict, aborter);
                                if (solverResult == null) {
                                    // perhaps one can try non-active constraints as well.
                                    // we currently do this only if prefiltering was used.
                                    // Note that this implies we will make to calls to the solver.
                                    if (!res.z) {
                                        return ResultFactory.unsuccessful();
                                    }
                                } else {
                                    // determine usable rules
                                    final Set<Variable<AfsProp>> usableVars = solverResult.y;
                                    final Map<Rule,GeneralizedRule> usableRuleMap = new LinkedHashMap<Rule,GeneralizedRule>(usableVars.size());
                                    for (final Map.Entry<Rule, Pair<GeneralizedRule,Variable<AfsProp>>> usable : res.x.entrySet()) {
                                        if (usableVars.contains(usable.getValue().y)) {
                                            usableRuleMap.put(usable.getKey(), usable.getValue().x);
                                        }
                                    }

                                    // and return result
                                    Pair<Map<Rule,Pair<TRSTerm,TRSTerm>>, Map<Rule,GeneralizedRule>> transformer;
                                    transformer = new Pair<Map<Rule,Pair<TRSTerm,TRSTerm>>, Map<Rule,GeneralizedRule>>(res.w, usableRuleMap);
                                    return QDPReductionPairProcessor.getResult(solverResult.x, origqdp, transformer, res.z);

                                }
                            }
                        } else {
                            QDPReductionPairProcessor.log.log(Level.INFO, "You tried to use active for applicative, but your solver does not support that! " +
                            "Therefore a-transformation is tried without active!\n");
                        }
                    }
                    if (tryNonactive) {
                        atransRes = qaur.getATransformedPR(P, usableRules);
                        if (atransRes != null) {
                            // we can atransform
                            P = new LinkedHashSet<Rule>(atransRes.x.values());
                            final Set<Rule> newSearchSubset = new LinkedHashSet<Rule>(searchSubset.size());
                            for (final Rule p : searchSubset) {
                                newSearchSubset.add(atransRes.x.get(p));
                            }
                            final Set<Rule> newNotSearchSubset = new LinkedHashSet<Rule>(notsearchSubset.size());
                            for (final Rule p : notsearchSubset) {
                                newNotSearchSubset.add(atransRes.x.get(p));
                            }
                            searchSubset    = newSearchSubset;
                            notsearchSubset = newNotSearchSubset;
                            usableRules = new LinkedHashSet<Rule>(atransRes.y.values());
                            // we have to ensure that it is not tried to use active any more.
                            useActive = false;
                        }
                    }
                }
            }
        }

        if (!allstrict && searchSubset.size() == 1) {
            allstrict = true;
        }

        Map<Rule, QActiveCondition> active;
        if (useActive) {
            final QUsableRules used = origqdp.getQUsableRulesCalculator();
            boolean mm = this.mergeMutual;
            if (solver instanceof QDPAfsOrderSolver && mm) {
                mm = false;
                QDPReductionPairProcessor.log.log(Level.WARNING, "Merge mutual is not compatible with QDPAfsOrderSolver!\n");
            }
            active = used.getActiveConditions(P, mm);
        } else {
            active = QUsableRules.getRulesAsConditionMap(usableRules);
        }

        // Put all pairs to the active condition map
        // so that every pair is oriented non-strictly
        final Map<Rule, QActiveCondition> heuristicActive = new LinkedHashMap<Rule, QActiveCondition>(active);
        for (final Rule p : notsearchSubset) {
            heuristicActive.put(p, QActiveCondition.TRUE);
        }
        aborter.checkAbortion();
        final QActiveOrder solvingOrder = solver.solveQActive(searchSubset, heuristicActive, useActive, allstrict, aborter);
//        QActiveOrder solvingOrder = solver.solveQActive(P, active, useActive, allstrict, aborter);
        if (solvingOrder != null) {
            return QDPReductionPairProcessor.getResult(solvingOrder, active, origqdp, atransRes,
                    this.scnpAsSizeChange);
        }
        return ResultFactory.unsuccessful();
    }

//  public Pair<? extends ExportableOrder<Term>, Set<Rule>> solve(QDPProblem transQDP, Abortion aborter) throws AbortionException;
    /**
     * Standard method to compute the result of a reduction pair processor.
     * @param order
     * @param UsableRules
     * @param origqdp
     * @param transformer
     * @param aTransQDP the A-transformed qdp problem or origqdp, if the problem was not a transformed
     * @return
     */
    public static Result getResult(
            final QActiveOrder order,
            final Map<Rule, QActiveCondition> active,
            final QDPProblem origqdp,
            final Pair<Map<Rule, Rule>, Map<Rule, Rule>> atransformer,
            final boolean scnpAsSizeChange) throws AbortionException {

        final Set<Rule> protoUsableRules = new LinkedHashSet<Rule>(active.size());
        for (final Map.Entry<Rule, QActiveCondition> entry : active.entrySet()) {
            if (order.checkQActiveCondition(entry.getValue())) {
                protoUsableRules.add(entry.getKey());
            }
        }

        return QDPReductionPairProcessor.getResult(order, protoUsableRules, origqdp, atransformer,
                scnpAsSizeChange);
    }

    static final class QDPApplicativeOrderProof extends QDPProof {

        private final Set<Rule> orientedPRules;
        private final Set<Rule> keptPRules;
        private final boolean filterTuple;
        private final Pair<Map<Rule,Pair<TRSTerm,TRSTerm>>,Map<Rule,GeneralizedRule>> atransformer;
        private final ExportableOrder<TRSTerm> order;
        private final QDPProblem origQDP;
        private final QDPProblem resultingQDP;

        QDPApplicativeOrderProof (
                final Set<Rule> orientedPRules,
                final Set<Rule> keptPRules,
                final ExportableOrder<TRSTerm> order,
                final Pair<Map<Rule,Pair<TRSTerm,TRSTerm>>,Map<Rule,GeneralizedRule>> atransformer,
                final boolean filterTuple,
                final QDPProblem origQDP,
                final QDPProblem resultingQDP
                ) {
            this.orientedPRules = orientedPRules;
            this.order = order;
            this.keptPRules = keptPRules;
            this.atransformer = atransformer;
            this.filterTuple = filterTuple;
            this.origQDP = origQDP;
            this.resultingQDP = resultingQDP;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) {
                result.append("We use the reduction pair processor "+o.cite(Citation.LPAR04)+".");
                if (this.filterTuple) {
                    result.append("First, we preprocessed all pairs by applying the argument filter which replaces every head" +
                    " symbol by its second argument. Then ");
                } else {
                    result.append("Here, ");
                }
                result.append("we combined the reduction pair processor ");
                result.append(o.cite(new Citation[]{Citation.LPAR04,Citation.JAR06}));
                result.append(" with the A-transformation ");
                result.append(o.cite(Citation.FROCOS05));
                result.append(" which results in the following intermediate Q-DP Problem."+o.linebreak());
                result.append(" The a-transformed P is "+o.cond_linebreak() + o.set(this.atransformer.x.values(), Export_Util.RULES)+o.cond_linebreak());
                result.append(" The a-transformed usable rules are "+o.cond_linebreak() + o.set(this.atransformer.y.values(), Export_Util.RULES)+o.cond_linebreak());
                result.append(o.paragraph()+o.cond_linebreak());
                result.append("The following pairs can be oriented strictly and are deleted.");
                result.append(o.cond_linebreak());
                result.append(o.set(this.orientedPRules, Export_Util.RULES));
                result.append("The remaining pairs can at least be oriented weakly.");
                result.append(o.cond_linebreak());
                result.append(o.set(this.keptPRules, Export_Util.RULES));
                result.append("Used ordering:  ");
                result.append(this.order.export(o));
                result.append(o.cond_linebreak());
                result.append("The following usable rules ");
                result.append(o.cite(Citation.FROCOS05));
                result.append(" with respect to the argument filtering of the ordering ");
                result.append(o.cite(Citation.JAR06));
                result.append(" were oriented:");
                result.append(o.cond_linebreak());
                result.append(o.set(this.atransformer.y.keySet(), Export_Util.RULES));
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultingQDP);
            }
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }

    static final class QDPOrderProof extends QDPProof {

        private final Set<Rule> orientedPRules;
        private final Set<Rule> keptPRules;
        private final Set<Rule> usableRules;
        private final ExportableOrder<TRSTerm> order;
        private final Pair<Map<Rule,Rule>,Map<Rule,Rule>> atransformer;
        private final QDPProblem origQDP;
        private final QDPProblem qdpProblem;
        private final boolean scnpAsSizeChange;

        public QDPOrderProof(
                final Set<Rule> orientedPRules,
                final Set<Rule> keptPRules,
                final ExportableOrder<TRSTerm> order,
                final Set<Rule> usableRules,
                final Pair<Map<Rule,Rule>,Map<Rule,Rule>> atransformer,
                final QDPProblem origQDP, final QDPProblem qdpProblem,
                final boolean scnpAsSizeChange) {
            this.orientedPRules = orientedPRules;
            this.order = order;
            this.keptPRules = keptPRules;
            this.usableRules = usableRules;
            this.atransformer = atransformer;
            this.origQDP = origQDP;
            this.qdpProblem = qdpProblem;
            this.scnpAsSizeChange = scnpAsSizeChange;
        }

        public QDPOrderProof(final Set<Rule> orientedPRules, final Set<Rule> keptPRules,
                final ExportableOrder<TRSTerm> order, final Set<Rule> usableRules,
                final Pair<Map<Rule, Rule>, Map<Rule, Rule>> atransformer,
                final QDPProblem origQDP, final QDPProblem qdpProblem) {
            this.orientedPRules = orientedPRules;
            this.order = order;
            this.keptPRules = keptPRules;
            this.usableRules = usableRules;
            this.atransformer = atransformer;
            this.origQDP = origQDP;
            this.qdpProblem = qdpProblem;
            this.scnpAsSizeChange = false;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) {
                result.append("We use the reduction pair processor ");
                result.append(o.cite(new Citation[]{Citation.LPAR04,Citation.JAR06}));
                result.append('.');
                if (this.atransformer != null) {
                    result.append(" Here, we combined the reduction pair processor with the A-transformation "+o.cite(Citation.FROCOS05));
                    result.append(" which results in the following intermediate Q-DP Problem."+o.linebreak());
                    result.append(" The a-transformed P is "+o.cond_linebreak() + o.set(this.atransformer.x.values(), Export_Util.RULES)+o.cond_linebreak());
                    result.append(" The a-transformed usable rules are "+o.cond_linebreak() + o.set(this.atransformer.y.values(), Export_Util.RULES)+o.cond_linebreak());
                }
                result.append(o.paragraph()+o.cond_linebreak());
                result.append("The following pairs can be oriented strictly and are deleted.");
                result.append(o.cond_linebreak());
                result.append(o.set(this.orientedPRules, Export_Util.RULES));
                result.append("The remaining pairs can at least be oriented weakly.");
                result.append(o.linebreak());
                //result.append(o.set(this.keptPRules, Export_Util.RULES));
                result.append("Used ordering:  ");
                result.append(this.order.export(o));
                result.append(o.cond_linebreak());
                result.append("The following usable rules ");
                result.append(o.cite(Citation.FROCOS05));
                result.append(" with respect to the argument filtering of the ordering ");
                result.append(o.cite(Citation.JAR06));
                result.append(" were oriented:");
                result.append(o.cond_linebreak());
                result.append(o.set(this.usableRules, Export_Util.RULES));
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            if (modus.isPositive()) {
                final Element proc;
                final Element dps = CPFTag.dps(doc, xmlMetaData, this.qdpProblem.getP());
                final Element scnpOrProc;
                if (this.usableRules.size() < this.origQDP.getR().size()) {
                    proc = CPFTag.RED_PAIR_UR_PROC.createElement(doc);
                    scnpOrProc = this.orderingConstraintProofToCPF(doc, xmlMetaData, proc);
                    proc.appendChild(dps);
                    proc.appendChild(CPFTag.USABLE_RULES.create(doc,
                            CPFTag.rules(doc, xmlMetaData, this.usableRules)));
                } else {
                    proc = CPFTag.RED_PAIR_PROC.createElement(doc);
                    scnpOrProc = this.orderingConstraintProofToCPF(doc, xmlMetaData, proc);
                    proc.appendChild(dps);
                }

                scnpOrProc.appendChild(childrenProofs[0]);

                return CPFTag.DP_PROOF.create(doc, scnpOrProc);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.qdpProblem);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return (this.atransformer == null && (!modus.isPositive() || this.order.isCPFSupported() == null));
        }

        @Override
        public String getNonCPFExportableReason(final CPFModus modus) {
            return super.getNonCPFExportableReason(modus) + (this.atransformer != null ? " + A-transformation" :
                " with " + this.order.isCPFSupported());
        }


        /**
         * @param doc to create the document
         * @param xmlMetaData for supporting meta data
         * @param proc the processor to be exported
         * @return the processor or scnp order, depending on the proof
         */
        private Element orderingConstraintProofToCPF(
            final Document doc,
            final XMLMetaData xmlMetaData,
            final Element proc)
        {
            if (this.order instanceof SCNPOrder) {
                final Element scnp;
                if (this.scnpAsSizeChange) {
                    try {
                        scnp = CPFTag.SIZE_CHANGE_PROC.createElement(doc);
                        scnp.appendChild(proc);
                        ((SCNPOrder) this.order).getSCNPGraphsToDOMWithP(doc, xmlMetaData, this.origQDP.getP(), scnp);
                        return scnp;
                    } catch (final DOMException e1) {
                        // TODO Auto-generated catch block
                        e1.printStackTrace();
                    } catch (final AbortionException e1) {
                        // TODO Auto-generated catch block
                        e1.printStackTrace();
                    }
                } else {
                    proc.appendChild(((SCNPOrder) this.order).toDOMSCNP(doc, xmlMetaData));
                    return proc;
                }
            } else {
                proc.appendChild(this.order.toCPF(doc, xmlMetaData));
            }
            return proc;
        }

    }

    /**
     * Standard method to compute the result of a reduction pair processor.
     * @param order
     * @param protoUsableRules
     * @param origqdp
     * @param atransformer null, if no a-transformation, mapping from P to A(P) and U(P,R) to A(U(P,R))
     * @return
     */
    public static Result getResult(
            final ExportableOrder<TRSTerm> order,
            final Set<Rule> protoUsableRules,
            final QDPProblem origqdp,
            final Pair<Map<Rule, Rule>, Map<Rule, Rule>> atransformer)
            throws AbortionException {
        return QDPReductionPairProcessor.getResult(order, protoUsableRules,
                origqdp, atransformer, false);
    }

    /**
     * Standard method to compute the result of a reduction pair processor.
     *
     * @param order
     * @param protoUsableRules
     * @param origqdp
     * @param atransformer
     *            null, if no a-transformation, mapping from P to A(P) and
     *            U(P,R) to A(U(P,R))
     * @param scnpAsSizeChange
     *            if we want to export scnp - order as a size change proof
     * @return
     */
    public static Result getResult(final ExportableOrder<TRSTerm> order,
            final Set<Rule> protoUsableRules, final QDPProblem origqdp,
            final Pair<Map<Rule, Rule>, Map<Rule, Rule>> atransformer,
            final boolean scnpAsSizeChange)
                throws AbortionException {

        final boolean usedATransformation = atransformer != null;



        // back transform usable rules if necessary
        Set<Rule> usableRules;
        if (usedATransformation) {
            usableRules = new LinkedHashSet<Rule>(protoUsableRules.size());
            for (final Map.Entry<Rule, Rule> transmap : atransformer.y.entrySet()) {
                if (protoUsableRules.contains(transmap.getValue())) {
                    usableRules.add(transmap.getKey());
                }
            }
        } else {
            usableRules = protoUsableRules;
        }

        // check which elements of P have been oriented strictly
        Set<Rule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        if (usedATransformation) {
            for (final Rule rule : origqdp.getP()) {
                final Rule arule = atransformer.x.get(rule);
                // only add non-strictly oriented pairs
                if (!order.solves(Constraint.fromRule(arule, OrderRelation.GR))) {
                    newPRules.add(rule);
                } else {
                    deletedPRules.add(rule);
                }
            }
        } else {
            for (final Rule rule : origqdp.getP()) {
                // only add non-strictly oriented rules
                if (!order.solves(Constraint.fromRule(rule, OrderRelation.GR))) {
                    newPRules.add(rule);
                } else {
                    deletedPRules.add(rule);
                }
            }
        }


        if (Globals.useAssertions) {
            final OrderRelation relation = OrderRelation.GE;
            for (Rule rule : usableRules) {
                if (usedATransformation) {
                    rule = atransformer.y.get(rule);
                }
                final Constraint<TRSTerm> constraint = Constraint.fromRule(rule, relation);
                final boolean result = order.solves(constraint);
                if (!result && Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION) {
                    System.err.println("Constraint not solved: " + constraint
                            + ", Order: " + order);
                }
                assert (result) : "Constraint not solved";
            }
            for (Rule rule : origqdp.getP()) {
                if (usedATransformation) {
                    rule = atransformer.x.get(rule);
                }
                final Constraint<TRSTerm> constraint = Constraint.fromRule(rule, relation);
                final boolean result = order.solves(constraint);
                if (!result && Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION) {
                    System.err.println("Constraint not solved: " + constraint
                            + ", Order: " + order);
                }
                assert (result) : "Constraint not solved";
            }
            assert(! deletedPRules.isEmpty()) : "No pairs were deleted.\nOrder: " + order;
            for (Rule rule : deletedPRules) {
                if (usedATransformation) {
                    rule = atransformer.x.get(rule);
                }
                assert (order.solves(Constraint.fromRule(rule, OrderRelation.GR))) :
                    "Deleted pair could not be strongly oriented.";
            }
        }

        // build smaller subproblem and proof
        final QDPProblem newQdp = origqdp.getSubProblem(ImmutableCreator.create(newPRules));
        final Proof proof = new QDPOrderProof(deletedPRules, newPRules, order,
                usableRules, atransformer, origqdp, newQdp, scnpAsSizeChange);

        // if we used an scnp order for proving and want to certify the proof,
        // we should have done this the allstrict - way
        if (scnpAsSizeChange && Options.certifier.isCeta()
                && order instanceof SCNPOrder
                && newQdp.getP().isEmpty()) {
            return ResultFactory.proved(proof);
        } else {
            return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT,
                    proof);
        }
    }


    /**
     * Standard method to compute the result of a reduction pair processor with
     * applicative active usable rules and tuple-symbols of DPs.
     * @param order
     * @param origqdp
     * @param transformer a mapping from dps to a-transed dps, and a mapping from usable rules to a-transed usable rules
     * @param filterTuple true iff DPs are preprocessed by filtering all tuple symbols to their second argument
     */
    public static Result getResult(
            final ExportableOrder<TRSTerm> order,
            final QDPProblem origqdp,
            final Pair<Map<Rule,Pair<TRSTerm,TRSTerm>>,Map<Rule,GeneralizedRule>> atransformer,
            final boolean filterTuple)
                throws AbortionException {


        // check which elements of P have been oriented strictly
        Set<Rule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        for (final Rule rule : origqdp.getP()) {
            final Pair<TRSTerm,TRSTerm> arule = atransformer.x.get(rule);
            // only add non-strictly oriented pairs
            if (!order.solves(Constraint.create(arule.x, arule.y, OrderRelation.GR))) {
                newPRules.add(rule);
            } else {
                deletedPRules.add(rule);
            }
        }


        if (Globals.useAssertions) {
            final OrderRelation relation = OrderRelation.GE;
            for (final GeneralizedRule rule : atransformer.y.values()) {
                assert (order.solves(Constraint.fromRule(rule, relation)));
            }
            for (final Rule rule : origqdp.getP()) {
                final Pair<TRSTerm,TRSTerm> arule = atransformer.x.get(rule);
                assert (order.solves(Constraint.create(arule.x, arule.y, relation)));
            }
            assert(! deletedPRules.isEmpty());
            for (final Rule rule : deletedPRules) {
                final Pair<TRSTerm,TRSTerm> arule = atransformer.x.get(rule);
                assert (order.solves(Constraint.create(arule.x, arule.y, OrderRelation.GR)));
            }
        }

        // build smaller subproblem and proof
        final QDPProblem newQdp = origqdp.getSubProblem(ImmutableCreator.create(newPRules));
        final Proof proof = new QDPApplicativeOrderProof(deletedPRules, newPRules, order, atransformer, filterTuple, origqdp, newQdp);
        return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);
    }

    public static class Arguments {
        public boolean active = true;
        public boolean allstrict = false;
        public boolean aTrans = true;
        public boolean mergeMutual = false;
        public SolverFactory order;
        public boolean usable = true;
        public boolean scnpAsSizeChange = false;
        public ReductionPairHeuristic heuristic;
    }

}
