package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;
import java.util.concurrent.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.Strategy.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 * @author MP
 */
public class SideConstraintStore {

    private final IDependencyGraph graph;

    private final ConcurrentHashMap<SideConstraintKey, ImmutablePair<ItpfBoolPolyVar<?>, ImplicationType>> sideConstraints;
    private final ConcurrentHashMap<IVariable<?>, SideConstraintKey> varToSideConstraint;
    private final ConcurrentHashMap<IDPProblem, ConcurrentHashMap<ItpfBoolPolyVar<?>, ItpfSchedulerVarProof<?>>> sideConstraintProofs;

    private final IDPSchedulerStrategy<Itpf, GenericItpfRule<?>> uraAtomStrategy = ItpfStrategy.DefaultStrategy.getStrategy();

    public SideConstraintStore(final IDependencyGraph graph) {
        this.graph = graph;
        this.sideConstraints = new ConcurrentHashMap<SideConstraintKey, ImmutablePair<ItpfBoolPolyVar<?>, ImplicationType>>();
        this.varToSideConstraint = new ConcurrentHashMap<IVariable<?>, SideConstraintStore.SideConstraintKey>();
        this.sideConstraintProofs = new ConcurrentHashMap<IDPProblem, ConcurrentHashMap<ItpfBoolPolyVar<?>,ItpfSchedulerVarProof<?>>>();
    }

    public void copySignatureFrom(final SideConstraintStore other) {
        this.sideConstraints.putAll(other.sideConstraints);
        this.varToSideConstraint.putAll(other.varToSideConstraint);
    }

    public Boolean isReplacement(final IVariable<?> var) {
        return this.varToSideConstraint.containsKey(var);
    }

    public Boolean hasReplacement(final Itpf precondition,
        final ItpfAtom atom,
        final ImplicationType implicationRequirement) {
        return !implicationRequirement.isSound()
            && (atom.isTermUra() || atom.isNodeUra() || atom.isEdgeUra());
    }

    public ImmutablePair<ItpfBoolPolyVar<?>, ImplicationType> getReplacement(final Itpf precondition,
        final ItpfAtom atom,
        final ImplicationType implicationRequirement) {
        if (Globals.useAssertions) {
            assert this.hasReplacement(precondition, atom,
                implicationRequirement) : "no replacement possible";
        }

        final SideConstraintKey key =
            this.getConstraintKey(precondition, atom,
                implicationRequirement);

        ImmutablePair<ItpfBoolPolyVar<?>, ImplicationType> res = this.sideConstraints.get(key);
        if (res == null) {
            res = this.createNewBoolPolyVar(atom);
            res = ConcurrentUtil.addToCache(this.sideConstraints, key, res);
            ConcurrentUtil.addToCache(this.varToSideConstraint, res.x.getPolyVar(), key);
        }

        return res;
    }

    public Map<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> getSideConstraints(final IDPProblem idp, final Collection<? extends IVariable<?>> usedVariables,
        final Abortion aborter) throws AbortionException {

        if (Globals.useAssertions) {
            assert idp.getIdpGraph().equals(this.graph) : "bad combination idp <-> graph";
        }

        final Set<IVariable<?>> processedVariables = new LinkedHashSet<IVariable<?>>();
        Collection<? extends IVariable<?>> varablesToProof = usedVariables;

        final Map<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>> result = new LinkedHashMap<ItpfBoolPolyVar<?>, ItpfSchedulerProof<Itpf, GenericItpfRule<?>>>();

        do {
            final Map<ItpfBoolPolyVar<?>, ItpfSchedulerVarProof<?>> newProofs =
                this.generateProofs(idp, varablesToProof, aborter);

            result.putAll(newProofs);

            processedVariables.addAll(varablesToProof);
            varablesToProof = this.collectVariables(newProofs.values());
            varablesToProof.removeAll(processedVariables);

            aborter.checkAbortion();
        } while (!varablesToProof.isEmpty());

        return result;
    }

    private Set<IVariable<?>> collectVariables(final Collection<? extends ItpfSchedulerVarProof<?>> proofs) {
        final LinkedHashSet<IVariable<?>> variables =
            new LinkedHashSet<IVariable<?>>();

        for (final ItpfSchedulerVarProof<?> proof : proofs) {
            for (final Itpf formula : proof.getLastFormulaStates()) {
                variables.addAll(formula.getVariables());
            }
        }

        return variables;
    }


    private Map<ItpfBoolPolyVar<?>, ItpfSchedulerVarProof<?>> generateProofs(final IDPProblem idp, final Collection<? extends IVariable<?>> varablesToProof, final Abortion aborter) throws AbortionException {
        final Map<ItpfBoolPolyVar<?>, ItpfSchedulerVarProof<?>> result = new LinkedHashMap<ItpfBoolPolyVar<?>, ItpfSchedulerVarProof<?>>();

        final List<ItpfSchedulerVarExecutorData<?>> workers =
            new ArrayList<ItpfSchedulerVarExecutorData<?>>(
                    varablesToProof.size());


        ConcurrentHashMap<ItpfBoolPolyVar<?>, ItpfSchedulerVarProof<?>> idpSideConstraintProofs =
            this.sideConstraintProofs.get(idp);
        if (idpSideConstraintProofs == null) {
            idpSideConstraintProofs = new ConcurrentHashMap<ItpfBoolPolyVar<?>, ItpfSchedulerVarProof<?>>();
            idpSideConstraintProofs = ConcurrentUtil.addToCache(this.sideConstraintProofs, idp, idpSideConstraintProofs);
        }

        for (final IVariable<?> var : varablesToProof) {
            final SideConstraintKey constraintKey = this.varToSideConstraint.get(var);

            if (constraintKey != null) {
                final ImmutablePair<ItpfBoolPolyVar<?>, ImplicationType> replacement =
                    this.sideConstraints.get(constraintKey);
                final ItpfSchedulerVarProof<?> proof = idpSideConstraintProofs.get(replacement.x);

                if (proof == null) {
                    workers.add(this.generateProofWorker(idp, replacement.x, replacement.y, constraintKey, aborter));
                } else {
                    result.put(replacement.x, proof);
                }
            }
        }

        final Map<ItpfBoolPolyVar<?>, Itpf> polySideConstraints = idp.getPolyInterpretation().getSideConstraints(varablesToProof);
        for (final Map.Entry<ItpfBoolPolyVar<?>, Itpf> polySideConstraint : polySideConstraints.entrySet()) {
            final ItpfSchedulerVarProof<?> proof = idpSideConstraintProofs.get(polySideConstraint.getKey());

            if (proof == null) {
                workers.add(this.generateProofWorker(idp, polySideConstraint.getKey(), polySideConstraint.getValue(), aborter));
            } else {
                result.put(polySideConstraint.getKey(), proof);
            }
        }

        MultithreadedExecutor.execute(workers, aborter);

        for (final ItpfSchedulerVarExecutorData<?> worker : workers) {
            ItpfSchedulerVarProof<?> proof = worker.getProof();
            proof = ConcurrentUtil.addToCache(idpSideConstraintProofs, proof.getVariable(), proof);
            result.put(proof.getVariable(), proof);
        }

        return result;
    }

    private <C extends SemiRing<C>> ItpfSchedulerVarExecutorData<?> generateProofWorker(final IDPProblem idp,
        final ItpfBoolPolyVar<C> var,
        final Itpf formula,
        final Abortion aborter) {
        return new ItpfSchedulerVarExecutorData<C>(idp, this.uraAtomStrategy, ImplicationType.COMPLETE, var, formula, aborter);
    }

    private <C extends SemiRing<C>> ItpfSchedulerVarExecutorData<?> generateProofWorker(final IDPProblem idp, final ItpfBoolPolyVar<C> var, final ImplicationType implication, final SideConstraintKey sideConstraintKey, final Abortion aborter) {
        final ItpfAtom atom = sideConstraintKey.getAtom();
        if (atom.isTermUra() || atom.isNodeUra() || atom.isEdgeUra()) {
            final ItpfAbstractUra ura = (ItpfAbstractUra) atom;
            IUsableRulesEstimation usableRulesEstimation = ura.getUsableRulesEstimation();

            if (usableRulesEstimation == null) {
                usableRulesEstimation = IUsableRulesEstimation.Estimations.getEstimation(IUsableRulesEstimation.Estimations.getDefaultEstimation());
            }

            final IDPUsableRulesResult usableRules;
            if (ura.isNodeUra()) {
                final ItpfNodeUra nodeUra = (ItpfNodeUra) ura;
                final ImmutablePolyTermSubstitution substitution = ImmutableTermToPolyTermSubstitution.create(nodeUra.getSubstitution(), this.graph.getPredefinedMap(), this.graph.getPolyInterpretation());
                usableRules = usableRulesEstimation.getUsableRules(idp, sideConstraintKey.getPrecondition(), nodeUra.getRelationalDependency(), nodeUra.getNode(), substitution);
            } else if (ura.isEdgeUra()) {
                final ItpfEdgeUra edgeUra = (ItpfEdgeUra) ura;
                final ImmutablePolyTermSubstitution substitution = ImmutableTermToPolyTermSubstitution.create(edgeUra.getSubstitution(), this.graph.getPredefinedMap(), this.graph.getPolyInterpretation());
                usableRules = usableRulesEstimation.getUsableRules(idp, sideConstraintKey.getPrecondition(), edgeUra.getRelationalDependency(), edgeUra.getActiveCondition(), edgeUra.getEdge(), substitution);
            } else if (ura.isTermUra()) {
                final ItpfTermUra termUra = (ItpfTermUra) ura;
                usableRules = usableRulesEstimation.getUsableRules(idp, sideConstraintKey.getPrecondition(), termUra.getRelationalDependency(), termUra.getActiveContext(), termUra.getTerm());
            } else {
                throw new UnsupportedOperationException("unknown URA type");
            }

            final ItpfFactory itpfFactory = idp.getItpfFactory();

            final Itpf usableRulesFormula = usableRules.getFormula();

            final ItpfImplication formulaToProove = itpfFactory.createImplication(itpfFactory.create(var, true, ITerm.EMPTY_SET), itpfFactory.create(usableRulesFormula.getClauses()));

            return new ItpfSchedulerVarExecutorData<C>(idp, this.uraAtomStrategy, ImplicationType.COMPLETE, var, itpfFactory.create(usableRulesFormula.getQuantification(), formulaToProove, true, ITerm.EMPTY_SET), aborter);
        } else {
            throw new IllegalArgumentException("unknown atom type: " + atom);
        }
    }

    private SideConstraintKey getConstraintKey(final Itpf precondition,
        final ItpfAtom atom,
        final ImplicationType implicationRequirement) {
        if (atom.isTermUra() || atom.isNodeUra() || atom.isEdgeUra()) {
            if (Globals.useAssertions) {
                assert !implicationRequirement.isSound();
            }
            return new SideConstraintKey(this.graph.getItpfFactory().createTrue(), atom, ImplicationType.COMPLETE);
        } else {
            throw new IllegalArgumentException("unknown atom type: " + atom);
        }
    }

    private ImmutablePair<ItpfBoolPolyVar<?>, ImplicationType> createNewBoolPolyVar(final ItpfAtom atom) {
        final String varPrefix;
        if (atom.isTermUra()) {
            varPrefix = "tURA";
        } else if (atom.isNodeUra()) {
            varPrefix = "nURA_" + ((ItpfNodeUra) atom).getNode().id;
        } else if (atom.isEdgeUra()) {
            final ItpfEdgeUra edgeURA = ((ItpfEdgeUra) atom);
            varPrefix = "eURA_" + edgeURA.getEdge().from.id + "_" + edgeURA.getEdge().to.id;
        } else {
            varPrefix = "bv";
        }

        final ItpfBoolPolyVar<?> boolVar = this.createNewBoolPolyVar(varPrefix, this.graph.getPolyInterpretation());

        return new ImmutablePair<ItpfBoolPolyVar<?>, ImplicationType> (boolVar, ImplicationType.COMPLETE);
    }

    private <C extends SemiRing<C>> ItpfBoolPolyVar<C> createNewBoolPolyVar(final String varName,
        final PolyInterpretation<C> polyInterpretation) {
        final ItpfBoolPolyVar<C> result = polyInterpretation.getConstraintFactory().createBoolPolyVar(
            polyInterpretation.getNextCoeff(varName, polyInterpretation.getBoolRange()),
            polyInterpretation);

        polyInterpretation.setExistQuantification(result.getPolyVar());

        return result;
    }

    private static class SideConstraintKey {

        private final Itpf precondition;
        private final ItpfAtom atom;
        private final ImplicationType implicationRequirement;
        private int hashCode;

        public SideConstraintKey(
                final Itpf precondition, final ItpfAtom atom,
                final ImplicationType implicationRequirement) {
            this.precondition = precondition;
            this.atom = atom;
            this.implicationRequirement = implicationRequirement;
            {
                final int prime = 31;
                int result = 1;
                result =
                    prime * result + ((atom == null) ? 0 : atom.hashCode());
                result = prime * result + implicationRequirement.hashCode();
                result = prime * result + precondition.hashCode();
                this.hashCode = result;
            }

        }

        public Itpf getPrecondition() {
            return this.precondition;
        }

        public ItpfAtom getAtom() {
            return this.atom;
        }

        public ImplicationType getImplicationRequirement() {
            return this.implicationRequirement;
        }

        @Override
        public int hashCode() {
            return this.hashCode;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (this.getClass() != obj.getClass()) {
                return false;
            }

            final SideConstraintKey other = (SideConstraintKey) obj;

            if (this.hashCode != other.hashCode()) {
                return false;
            }

            return this.atom.equals(other.atom)
                && this.precondition.equals(other.precondition)
                && this.implicationRequirement.equals(other.implicationRequirement);
        }

    }

}