package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author mpluecke
 */
public abstract class AbstractInitialGraphProcessor extends AbstractGraphProcessor {

    protected AbstractInitialGraphProcessor() {
        super();
    }

    public abstract IIDependencyGraph createInitialGraph(IDPRuleAnalysis ruleAnalysis, Abortion aborter) throws AbortionException;

    /**
     * @param ruleAnalysis
     * @param aborter
     * @return x: nodes, y: maxNodeId, z: locked variables
     */
    public static Triple<Set<Node>, Integer, Set<TRSVariable>> createInitialNodes(IDPRuleAnalysis ruleAnalysis, Abortion aborter) {
        Set<Node> nodes = new LinkedHashSet<Node>();
        int maxNodeId = -1;
        FreshNameGenerator freshNames = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        Set<TRSVariable> lockedVars = new LinkedHashSet<TRSVariable>();
        for (GeneralizedRule rule : ruleAnalysis.getPAnalysis().getRules()) {
            Set<TRSVariable> ruleVars = rule.getVariables();
            Map<TRSVariable, TRSVariable> subst = new LinkedHashMap<TRSVariable, TRSVariable>();
            Map<TRSVariable, TRSVariable> loopSubst = new LinkedHashMap<TRSVariable, TRSVariable>();
            int newNodeId = ++maxNodeId;
            for (TRSVariable v : ruleVars) {
                String newName = freshNames.getFreshName(v.getName() + "[" + newNodeId + "]", false);
                TRSVariable newVar;
                if (!newName.equals(v.getName())) {
                    newVar = TRSTerm.createVariable(newName);
                    lockedVars.add(newVar);
                    subst.put(v, newVar);
                } else {
                    newVar = v;
                    lockedVars.add(v);
                }
                {
                    String newLoopName = freshNames.getFreshName(newName, false);
                    TRSVariable newLoopVar = TRSTerm.createVariable(newLoopName);
                    lockedVars.add(newLoopVar);
                    loopSubst.put(newVar, newLoopVar);
                }
            }
            TRSSubstitution varRename = TRSSubstitution.create(ImmutableCreator.create(subst), true);
            if (subst.isEmpty()) {
                nodes.add(new Node(rule, newNodeId, ImmutableCreator.create(loopSubst)));
            } else {
                nodes.add(new Node(GeneralizedRule.create(
                        rule.getLeft().applySubstitution(varRename),
                        rule.getRight().applySubstitution(varRename),
                        rule.getLhsInStandardRepresentation(),
                        rule.getRhsInStandardRepresentation()
                        ), newNodeId, ImmutableCreator.create(loopSubst)));
            }
        }
        return new Triple<Set<Node>, Integer, Set<TRSVariable>>(nodes, maxNodeId, lockedVars);
    }

}
