package aprove.verification.dpframework.IDPProblem.Processors.cgirp;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.itpfExecution.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.itpf.IItpfRule.*;
import aprove.verification.dpframework.IDPProblem.itpf.rules.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class CCNodeCondition<PathHeuristicData extends IPathHeuristic.Data> implements INodeConditionFunction {

    private final IPathGenerator pathGenerator;
    private final ImmutableList<IItpfRule> itpfProcs;

    @ParamsViaArgumentObject
    public CCNodeCondition(Arguments<PathHeuristicData> arguments) {
        this(arguments.pathGenerator);
    }

    public CCNodeCondition(IPathGenerator pathGenerator) {
        this.pathGenerator = pathGenerator;
        this.itpfProcs = ImmutableCreator.create(Arrays.asList(new IItpfRule[] {new CCRelOp()}));
    }

    @Override
    public List<ImmutablePair<ConditionalConstraint, DefaultProof>> createNodeCondition(IDPProblem idp, Node dp,
            Itpf conclusion, Abortion aborter) throws AbortionException {

        Map<IItpfRule, Set<IItpfRule>> ruleGroupings = new LinkedHashMap<IItpfRule, Set<IItpfRule>>();
        // TODO group rules

        List<PathExecutorData> workers = new ArrayList<PathExecutorData>(idp.getIdpGraph().getEdges().size());

        List<Pair<Integer, ? extends List<Node>>> paths = this.pathGenerator.paths(idp.getIdpGraph(), dp);

        for (Pair<Integer, ? extends List<Node>> path : paths) {
            VariableRenamedPath renamedPath = VariableRenamedPath.create(path.y);
            TRSSubstitution conclusionSigma = TRSSubstitution.create(renamedPath.getPath().get(path.x).y);
            ConditionalConstraint cc = ConditionalConstraint.create(
                    ItpfNeg.create(idp.getIdpGraph().itpfPath(renamedPath)),
                    conclusion.applySubstitution(conclusionSigma)
            );
            workers.add(new PathExecutorData(idp, renamedPath, cc, this.itpfProcs, ruleGroupings, ApplicationMode.Multistep, aborter));
        }
        MultithreadedExecutor.execute(workers, aborter);

        List<ImmutablePair<ConditionalConstraint, DefaultProof>> result = new ArrayList<ImmutablePair<ConditionalConstraint, DefaultProof>>(workers.size());
        for (PathExecutorData worker : workers) {
            result.add(new ImmutablePair<ConditionalConstraint, DefaultProof>(worker.getResult(), worker.getProof()));
        }

        return result;
    }

    protected boolean hasDivMod(Itpf formula, IDPPredefinedMap predefinedMap) {
        Set<FunctionSymbol> symbols = formula.getFunctionSymbols();
        for (FunctionSymbol fs : symbols) {
            if (predefinedMap.isDivOrMod(fs)) {
                return true;
            }
        }
        return false;
    }

    public static class Arguments<PathHeuristicData extends IPathHeuristic.Data> {

        public IPathGenerator pathGenerator;

    }

    public static class Proof extends DefaultProof {

        protected final ImmutableList<PathProof> pathProofs;

        public Proof (ImmutableList<PathProof> pathProofs) {
            this.pathProofs = pathProofs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            Iterator<PathProof> iter = this.pathProofs.iterator();
            while(iter.hasNext()) {
                PathProof proof = iter.next();
                sb.append(proof.export(o, level));
                if (iter.hasNext()) {
                    sb.append(o.linebreak());
                }
            }
            return sb.toString();
        }
    }

    protected static class PathExecutorData extends ItpfSchedulerExecutorData<PathProof> {

        protected final VariableRenamedPath path;
        protected final ConditionalConstraint cc;
        protected Itpf resultConstraint;

        public PathExecutorData(IDPProblem idp, VariableRenamedPath path, ConditionalConstraint cc, ImmutableList<IItpfRule> rules,
                Map<IItpfRule, Set<IItpfRule>> ruleGrouping,
                ApplicationMode mode, Abortion aborter) {
            super(idp, rules, ruleGrouping, mode, aborter);
            this.path = path;
            this.cc = cc;

        }

        @Override
        protected PathProof createInitialProof() {
            return new PathProof(this.path, this.getInitialFormula(), this.ruleGrouping);
        }

        @Override
        protected Itpf getInitialFormula() {
            return this.cc.getCondition();
        }

        public ConditionalConstraint getResult() {
            return ConditionalConstraint.create(this.result, this.cc.getCondition());
        }
    }


    public static class PathProof extends ItpfSchedulerProof {

        private final VariableRenamedPath path;
        private final Itpf pathFormula;

        public PathProof(VariableRenamedPath path, Itpf pathFormula, Map<IItpfRule, Set<IItpfRule>> ruleGrouping) {
            super(ruleGrouping);
            this.path = path;
            this.pathFormula = pathFormula;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return this.export(o, null, level);
        }

        @Override
        public String export(Export_Util o, IDPPredefinedMap predefinedMap,
                VerbosityLevel verbosityLevel) {
            StringBuilder sb = new StringBuilder();
            sb.append("We consider the variable renamed path fragment: ");
            sb.append(o.linebreak());
            sb.append(this.path.export(o, predefinedMap, verbosityLevel));
            sb.append("The resulting formula is: ");
            sb.append(o.linebreak());
            sb.append(this.pathFormula.export(o, predefinedMap, verbosityLevel));
            sb.append("It is transformed the following way:");
            sb.append(o.linebreak());
            this.exportSteps(sb, o, predefinedMap, verbosityLevel);
            return sb.toString();
        }

    }

}
