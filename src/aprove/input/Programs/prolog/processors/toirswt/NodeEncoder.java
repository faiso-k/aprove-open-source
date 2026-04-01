package aprove.input.Programs.prolog.processors.toirswt;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.graph.rules.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

class NodeEncoder {

    private final PrologEvaluationGraph graph;
    private final GroundnessAnalysis groundnessAnalysis;

    private final NodeToTermConverter nodeToTermConverter = new NodeToTermConverter();
    private final RuleFactory ruleFactory = new RuleFactory();
    private final PrologToIRSwTEncoder prologToIRSwTEncoder = new PrologToIRSwTEncoder();

    private final FreshNameGenerator fng;
    private final Abortion aborter;

    public NodeEncoder(PrologEvaluationGraph graph,
            GroundnessAnalysis groundnessAnalysis,
            FreshNameGenerator fng, Abortion aborter) {
        this.graph = graph;
        this.groundnessAnalysis = groundnessAnalysis;
        this.fng = fng;
        this.aborter = aborter;
    }

    public TRSFunctionApplication encodeRootIn() {
        return this.nodeToTermConverter.getInSymbol(this.graph.getRoot());
    }

    public Collection<IGeneralizedRule> encodePathsToCycle(Cycle<PrologAbstractState> scc) {
        final Collection<IGeneralizedRule> returnValue = new LinkedList<>();
        for(List<Node<PrologAbstractState>> pathToScc : this.getNonLoopingPathsToScc(scc)) {
            for(Node<PrologAbstractState> pathNode : pathToScc) {
                returnValue.addAll(this.encodeNode(pathNode));
            }
        }
        return returnValue;
    }

    private Collection<List<Node<PrologAbstractState>>> getNonLoopingPathsToScc(Cycle<PrologAbstractState> scc) {
        final Collection<List<Node<PrologAbstractState>>> returnValue = new HashSet<>();
        final List<Node<PrologAbstractState>> initialPath = new LinkedList<>();
        initialPath.add(this.graph.getRoot());

        final Queue<List<Node<PrologAbstractState>>> workQueue = new LinkedList<>();
        workQueue.add(initialPath);
        while(!workQueue.isEmpty()) {
            final List<Node<PrologAbstractState>> currentPath = workQueue.poll();
            final Node<PrologAbstractState> lastNode = currentPath.get(currentPath.size() - 1);
            if(scc.contains(lastNode)) {
                returnValue.add(currentPath);
            } else {
                for(Node<PrologAbstractState> succNode : this.graph.getOut(lastNode)) {
                    if(!currentPath.contains(succNode)) {
                        final List<Node<PrologAbstractState>> succPath = new LinkedList<>(currentPath);
                        succPath.add(succNode);
                        workQueue.add(succPath);
                    }
                }
            }
        }

        return returnValue;
    }

    /**
     * The encoding of nodes as terms of an IRSwT is defined in A. Weinert's Master Thesis.
     * @param node Some node. Must be contained in the graph given on creation of this encoder. Must not be null.
     * @return A collection of rules that encodes the given node in an IRSwT. Is not null.
     */
    public Collection<IGeneralizedRule> encodeNode(Node<PrologAbstractState> node) {
        assert this.graph.contains(node);

        if(this.graph.isSuccessNode(node)) {
            return this.encodeSuccessNode(node);
        } else if (this.graph.isUnifyCaseNode(node)) {
            return this.encodeUnifyNode(node);
        } else if (this.graph.isUnifySuccessNode(node)) {
            return this.encodeUnifyNode(node);
        } else if (this.graph.isUnifyFailNode(node)) {
            return this.encodeUnifyNode(node);
        } else if (this.graph.isCaseNode(node)) {
            return this.encodeCaseNode(node);
        } else if (this.graph.isOnlyEvalNode(node)) {
            return this.encodeOnlyEvalNode(node);
        } else if (this.graph.isEvalNode(node)) {
            return this.encodeEvalNode(node);
        } else if (this.graph.isBacktrackNode(node)) {
            return this.encodeBacktrackNode(node);
        } else if (this.graph.isCutNode(node)) {
            return this.encodeCutNode(node);
        } else if (this.graph.isFailNode(node)) {
            return this.encodeFailNode(node);
        } else if (this.graph.isArithCompNode(node)) {
            return this.encodeArithCompNode(node);
        } else if (this.graph.isIsNode(node)) {
            return this.encodeIsNode(node);
        } else if (this.graph.isInstanceNode(node)) {
            return this.encodeInstanceNode(node);
        } else if (this.graph.isGeneralizationNode(node)) {
            return this.encodeGeneralizationNode(node);
        } else if (this.graph.isSplitNode(node)) {
            return this.encodeSplitNode(node);
        } else if (this.graph.isParallelNode(node)) {
            return this.encodeParallelNode(node);
        } else if (this.graph.isLeaf(node, false)) {
            return this.encodeLeaf(node);
        } else if (this.graph.isCallNode(node)) {
            return this.encodeCallNode(node);
        } else if (this.graph.isNotNode(node)) {
            return this.encodeNotNode(node);
        } else {
            assert false : "Unknown node type";
            return null;
        }
    }

    private Collection<IGeneralizedRule> encodeUnifyNode(
            Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        final Node<PrologAbstractState> successSucc = this.getUnifySuccessSucc(node);
        if(successSucc != null) {
            final Substitution successSubstitution = this.getUnifySuccessSubstitution(node);

            final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(successSucc);
            final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(successSucc);

            returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn.applySubstitution(successSubstitution)));
            returnValue.add(this.ruleFactory.createUnconditionalRule(succOut.applySubstitution(successSubstitution), nodeOut));
        }

        final Node<PrologAbstractState> failSucc = this.getUnifyFailSucc(node);
        if(failSucc != null) {
            final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(failSucc);
            final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(failSucc);

            returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn));
            returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut));
        }

        assert successSucc != null || failSucc != null;
        return returnValue;
    }

    private Substitution getUnifySuccessSubstitution(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.UNIFY_SUCCESS) {
                return this.prologToIRSwTEncoder.convertPrologSubstitution(((UnifySuccessRule)edge.getObject()).getSubstitution());
            } else if(edge.getObject().rule() == AbstractInferenceRules.UNIFY_CASE) {
                if(((UnifyCaseRule)edge.getObject()).getSubstitution() != null) {
                    return this.prologToIRSwTEncoder.convertPrologSubstitution(((UnifyCaseRule)edge.getObject()).getSubstitution());
                }
            }
        }
        assert false;
        return null;
    }

    private Node<PrologAbstractState> getUnifySuccessSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.UNIFY_SUCCESS) {
                return edge.getEndNode();
            } else if(edge.getObject().rule() == AbstractInferenceRules.UNIFY_CASE) {
                if(((UnifyCaseRule)edge.getObject()).getSubstitution() != null) {
                    return edge.getEndNode();
                }
            }
        }
        return null;
    }

    private Node<PrologAbstractState> getUnifyFailSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.UNIFY_FAIL) {
                return edge.getEndNode();
            } else if(edge.getObject().rule() == AbstractInferenceRules.UNIFY_CASE) {
                if(((UnifyCaseRule)edge.getObject()).getClash() != null) {
                    return edge.getEndNode();
                }
            }
        }
        return null;
    }

    private Collection<IGeneralizedRule> encodeNotNode(Node<PrologAbstractState> node) {
        final Collection<Node<PrologAbstractState>> succs = this.graph.getOut(node);
        assert succs.size() == 1;

        final Node<PrologAbstractState> succ = succs.iterator().next();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(succ);
        final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(succ);

        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut));

        return returnValue;
    }

    private Collection<IGeneralizedRule> encodeCallNode(Node<PrologAbstractState> node) {
        final Collection<Node<PrologAbstractState>> succs = this.graph.getOut(node);
        assert succs.size() == 1;

        final Node<PrologAbstractState> succ = succs.iterator().next();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(succ);
        final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(succ);

        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut));

        return returnValue;
    }

    private Collection<IGeneralizedRule> encodeLeaf(Node<PrologAbstractState> node) {
        return Collections.emptySet();
    }

    private Collection<IGeneralizedRule> encodeSuccessNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, nodeOut));

        return returnValue;
    }

    private Collection<IGeneralizedRule> encodeCaseNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        assert this.graph.getOut(node).size() == 1 : "Case node with not exactly one successor";
        final Node<PrologAbstractState> successor = this.graph.getOut(node).iterator().next();

        final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(successor);
        final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(successor);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut));

        return returnValue;
    }

    private Collection<IGeneralizedRule> encodeOnlyEvalNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        assert this.graph.getOut(node).size() == 1 : "Only eval node with not exactly one successor";
        final Node<PrologAbstractState> successor = this.graph.getOut(node).iterator().next();
        final Substitution evalSubstitution = this.getEvalOnlySubstitution(node);

        final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(successor);
        final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(successor);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn.applySubstitution(evalSubstitution), succIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut.applySubstitution(evalSubstitution)));

        return returnValue;
    }

    private Substitution getEvalOnlySubstitution(Node<PrologAbstractState> node) {
        final PrologSubstitution prologSubst = ((OnlyEvalRule)this.graph.getOutEdges(node).iterator().next().getObject()).getSubstitution();
        return this.prologToIRSwTEncoder.convertPrologSubstitution(prologSubst);
    }

    private Collection<IGeneralizedRule> encodeEvalNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        assert this.graph.getOut(node).size() == 2 : "Eval node with not exactly two successors";

        final Node<PrologAbstractState> successSuccessor = this.getEvalSuccessSuccessor(node);
        final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(successSuccessor);
        final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(successSuccessor);

        final Substitution evalSubstitution = this.getEvalSubstitution(node);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn.applySubstitution(evalSubstitution), succIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut.applySubstitution(evalSubstitution)));

        final Node<PrologAbstractState> failSuccessor = this.getEvalBacktrackSuccessor(node);
        final TRSFunctionApplication failIn = this.nodeToTermConverter.getInSymbol(failSuccessor);
        final TRSFunctionApplication failOut = this.nodeToTermConverter.getOutSymbol(failSuccessor);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, failIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(failOut, nodeOut));

        return returnValue;
    }

    private Node<PrologAbstractState> getEvalSuccessSuccessor(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> outEdge : this.graph.getOutEdges(node)) {
            if(outEdge.getObject().rule() == AbstractInferenceRules.EVAL && ((EvalRule)outEdge.getObject()).getClash() == null) {
                return outEdge.getEndNode();
            }
        }
        assert false : "No eval success rule found";
        return null;
    }

    private Node<PrologAbstractState> getEvalBacktrackSuccessor(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> outEdge : this.graph.getOutEdges(node)) {
            if(outEdge.getObject().rule() == AbstractInferenceRules.EVAL && ((EvalRule)outEdge.getObject()).getClash() != null) {
                return outEdge.getEndNode();
            }
        }
        assert false : "No eval backtrack rule found";
        return null;
    }

    private Substitution getEvalSubstitution(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> outEdge : this.graph.getOutEdges(node)) {
            if(outEdge.getObject().rule() == AbstractInferenceRules.EVAL && ((EvalRule)outEdge.getObject()).getClash() == null) {
                return this.prologToIRSwTEncoder.convertPrologSubstitution(((EvalRule)outEdge.getObject()).getSubstitution());
            }
        }
        assert false : "No eval success rule found";
        return null;
    }

    private Collection<IGeneralizedRule> encodeBacktrackNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        assert this.graph.getOut(node).size() == 1 : "Backtrack node with not exactly one successor";
        final Node<PrologAbstractState> successor = this.graph.getOut(node).iterator().next();

        final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(successor);
        final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(successor);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut));

        return returnValue;
    }

    private Collection<IGeneralizedRule> encodeCutNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        assert this.graph.getOut(node).size() == 1 : "Cut node with not exactly one successor";
        final Node<PrologAbstractState> successor = this.graph.getOut(node).iterator().next();

        final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(successor);
        final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(successor);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut));

        return returnValue;
    }

    private Collection<IGeneralizedRule> encodeFailNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        assert this.graph.getOut(node).size() == 1 : "Fail node with not exactly one successor";
        final Node<PrologAbstractState> successor = this.graph.getOut(node).iterator().next();

        final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(successor);
        final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(successor);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut));

        return returnValue;
    }

    private Collection<IGeneralizedRule> encodeArithCompNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        final Node<PrologAbstractState> errorSuccessor = this.getArithCompErrorSucc(node);
        if(errorSuccessor != null) {
            final TRSFunctionApplication errorIn = this.nodeToTermConverter.getInSymbol(errorSuccessor);
            final TRSFunctionApplication errorOut = this.nodeToTermConverter.getOutSymbol(errorSuccessor);

            returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, errorIn));
            returnValue.add(this.ruleFactory.createUnconditionalRule(errorOut, nodeOut));
        }

        final Node<PrologAbstractState> trueSuccessor = this.getArithCompTrueSucc(node);
        if(trueSuccessor != null) {
            final TRSFunctionApplication trueIn = this.nodeToTermConverter.getInSymbol(trueSuccessor);
            final TRSFunctionApplication trueOut = this.nodeToTermConverter.getOutSymbol(trueSuccessor);

            PrologTerm prologTerm = node.getObject().getHeadOfState().getTerm();
            if(prologTerm.isConjunction()) {
                prologTerm = prologTerm.conjunctionHead();
            }
            final TRSFunctionApplication comparison = (TRSFunctionApplication) this.prologToIRSwTEncoder.convertPrologTermToIRSwTTerm(prologTerm);

            returnValue.add(this.ruleFactory.createConditionalRule(nodeIn, trueIn, comparison));
            returnValue.add(this.ruleFactory.createConditionalRule(trueOut, nodeOut, comparison));
        }

        final Node<PrologAbstractState> falseSuccessor = this.getArithCompFalseSucc(node);
        if(falseSuccessor != null) {
            final TRSFunctionApplication errorIn = this.nodeToTermConverter.getInSymbol(falseSuccessor);
            final TRSFunctionApplication errorOut = this.nodeToTermConverter.getOutSymbol(falseSuccessor);

            PrologTerm prologTerm = node.getObject().getHeadOfState().getTerm();
            if(prologTerm.isConjunction()) {
                prologTerm = prologTerm.conjunctionHead();
            }
            final TRSFunctionApplication comparison = (TRSFunctionApplication) this.prologToIRSwTEncoder.convertPrologTermToIRSwTTerm(prologTerm);
            final TRSFunctionApplication negatedComparison = this.negateArithComp(comparison);

            returnValue.add(this.ruleFactory.createConditionalRule(nodeIn, errorIn, negatedComparison));
            returnValue.add(this.ruleFactory.createConditionalRule(errorOut, nodeOut, negatedComparison));
        }

        return returnValue;

    }

    private Node<PrologAbstractState> getArithCompErrorSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.ARITHCOMP_ERROR) {
                return edge.getEndNode();
            }
        }
        return null;
    }

    private Node<PrologAbstractState> getArithCompTrueSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.ARITHCOMP_SUCCESS) {
                return edge.getEndNode();
            }
        }
        return null;
    }

    private Node<PrologAbstractState> getArithCompFalseSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.ARITHCOMP_FAIL) {
                return edge.getEndNode();
            }
        }
        return null;
    }

    private Collection<IGeneralizedRule> encodeIsNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        final Node<PrologAbstractState> errorSuccessor = this.getIsErrorSucc(node);
        if(errorSuccessor != null) {
            final TRSFunctionApplication errorIn = this.nodeToTermConverter.getInSymbol(errorSuccessor);
            final TRSFunctionApplication errorOut = this.nodeToTermConverter.getOutSymbol(errorSuccessor);

            returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, errorIn));
            returnValue.add(this.ruleFactory.createUnconditionalRule(errorOut, nodeOut));
        }

        final Node<PrologAbstractState> trueSuccessor = this.getIsTrueSucc(node);
        if(trueSuccessor != null) {
            final TRSFunctionApplication trueIn = this.nodeToTermConverter.getInSymbol(trueSuccessor);
            final TRSFunctionApplication trueOut = this.nodeToTermConverter.getOutSymbol(trueSuccessor);

            final Substitution substitution = this.getIsSubstitution(node);
            final TRSFunctionApplication comparison = this.getIsRelation(node).applySubstitution(substitution);

            returnValue.add(this.ruleFactory.createConditionalRule(nodeIn.applySubstitution(substitution), trueIn, comparison));
            returnValue.add(this.ruleFactory.createUnconditionalRule(trueOut, nodeOut.applySubstitution(substitution)));
        }

        final Node<PrologAbstractState> falseSuccessor = this.getIsFalseSucc(node);
        if(falseSuccessor != null) {
            final TRSFunctionApplication errorIn = this.nodeToTermConverter.getInSymbol(falseSuccessor);
            final TRSFunctionApplication errorOut = this.nodeToTermConverter.getOutSymbol(falseSuccessor);

            final TRSFunctionApplication comparison = this.getIsRelation(node);
            final TRSFunctionApplication negatedComparison = this.negateArithComp(comparison);

            returnValue.add(this.ruleFactory.createConditionalRule(nodeIn, errorIn, negatedComparison));
            returnValue.add(this.ruleFactory.createUnconditionalRule(errorOut, nodeOut));
        }

        return returnValue;

    }

    private Substitution getIsSubstitution(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.IS_SUCCESS) {
                return this.prologToIRSwTEncoder.convertPrologSubstitution(((IsSuccessRule)edge.getObject()).getSubstitution());
            }
        }
        return null;
    }

    private TRSFunctionApplication getIsRelation(Node<PrologAbstractState> node) {
        PrologTerm firstTerm =  node.getObject().getHeadOfState().getTerm();
        if(firstTerm.isConjunction()) {
            firstTerm = firstTerm.conjunctionHead();
        }

        assert firstTerm.getName().equals(PrologBuiltin.IS_NAME);

        return TRSTerm.createFunctionApplication(FunctionSymbol.create("=", 2),
                firstTerm.getArgument(0).toTerm(),
                firstTerm.getArgument(1).toTerm());
    }

    private Node<PrologAbstractState> getIsErrorSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.IS_ERROR) {
                return edge.getEndNode();
            }
        }
        return null;
    }

    private Node<PrologAbstractState> getIsTrueSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.IS_SUCCESS) {
                return edge.getEndNode();
            }
        }
        return null;
    }

    private Node<PrologAbstractState> getIsFalseSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.IS_FAIL) {
                return edge.getEndNode();
            }
        }
        return null;
    }

    private Collection<IGeneralizedRule> encodeInstanceNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication instanceIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication instanceOut = this.nodeToTermConverter.getOutSymbol(node);

        final Substitution edgeSubstitution = this.getInstanceSubstitution(node);
        final Node<PrologAbstractState> general = this.getInstanceSuccessor(node);

        final TRSFunctionApplication generalIn = this.nodeToTermConverter.getInSymbol(general).applySubstitution(edgeSubstitution);
        final TRSFunctionApplication generalOut = this.nodeToTermConverter.getOutSymbol(general).applySubstitution(edgeSubstitution);

        returnValue.add(this.ruleFactory.createUnconditionalRule(instanceIn, generalIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(generalOut, instanceOut));

        return returnValue;
    }

    /**
     * @param node Some node. Must be an instance node in this.graph.
     * @return The substitution associated with this nodes outgoing instance-edge. Is not null.
     */
    private Substitution getInstanceSubstitution(Node<PrologAbstractState> node) {
        assert node != null;
        assert this.graph.isInstanceNode(node);

        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.INSTANCE) {
                return this.prologToIRSwTEncoder.convertPrologSubstitution(((InstanceRule)edge.getObject()).getMatcher());
            }
        }

        assert false : "No instance substitution found";
        return null;
    }

    private Node<PrologAbstractState> getInstanceSuccessor(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.INSTANCE) {
                return edge.getEndNode();
            }
        }
        assert false : "No instance successor found";
        return null;
    }

    private Collection<IGeneralizedRule> encodeGeneralizationNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication instanceIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication instanceOut = this.nodeToTermConverter.getOutSymbol(node);

        final Substitution edgeSubstitution = this.getGeneralizationSubstitution(node);
        final Node<PrologAbstractState> general = this.getGeneralizationSuccessor(node);

        final TRSFunctionApplication generalIn = this.nodeToTermConverter.getInSymbol(general).applySubstitution(edgeSubstitution);
        final TRSFunctionApplication generalOut = this.nodeToTermConverter.getOutSymbol(general).applySubstitution(edgeSubstitution);

        returnValue.add(this.ruleFactory.createUnconditionalRule(instanceIn, generalIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(generalOut, instanceOut));

        return returnValue;
    }

    private Substitution getGeneralizationSubstitution(Node<PrologAbstractState> node) {
        assert node != null;
        assert this.graph.isGeneralizationNode(node);

        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.GENERALIZATION) {
                return this.prologToIRSwTEncoder.convertPrologSubstitution(((GeneralizationRule)edge.getObject()).getGeneralizationAsSubstitution());
            }
        }

        assert false : "No generalization substitution found";
        return null;
    }

    private Node<PrologAbstractState> getGeneralizationSuccessor(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.GENERALIZATION) {
                return edge.getEndNode();
            }
        }
        assert false : "No generalization successor found";
        return null;
    }

    private Collection<IGeneralizedRule> encodeSplitNode(Node<PrologAbstractState> node) {
        assert this.graph.getOut(node).size() == 2 : "Unexpected Split node without two sucessors";
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        final Node<PrologAbstractState> splitLhs = this.getLhsSplitSucc(node);
        final TRSFunctionApplication lhsIn = this.nodeToTermConverter.getInSymbol(splitLhs);
        final TRSFunctionApplication lhsOut = this.nodeToTermConverter.getOutSymbol(splitLhs);

        final Node<PrologAbstractState> splitRhs = this.getRhsSplitSucc(node);
        final TRSFunctionApplication rhsIn = this.nodeToTermConverter.getInSymbol(splitRhs);
        final TRSFunctionApplication rhsOut = this.nodeToTermConverter.getOutSymbol(splitRhs);

        returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, lhsIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(lhsOut, rhsIn));
        returnValue.add(this.ruleFactory.createUnconditionalRule(rhsOut, nodeOut));

        return returnValue;
    }

    private Node<PrologAbstractState> getLhsSplitSucc(Node<PrologAbstractState> node) {
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.SPLIT) {
                return edge.getEndNode();
            }
        }
        assert false : "No lhs split successor found";
        return null;
    }

    private Node<PrologAbstractState> getRhsSplitSucc(Node<PrologAbstractState> node) {
        boolean foundFirst = false;
        for(Edge<AbstractInferenceRule, PrologAbstractState> edge : this.graph.getOutEdges(node)) {
            if(edge.getObject().rule() == AbstractInferenceRules.SPLIT) {
                if(foundFirst) {
                    return edge.getEndNode();
                } else {
                    foundFirst = true;
                }
            }
        }
        assert false : "No rhs split successor found";
        return null;
    }

    private Collection<IGeneralizedRule> encodeParallelNode(Node<PrologAbstractState> node) {
        final Collection<IGeneralizedRule> returnValue = new HashSet<>();

        final TRSFunctionApplication nodeIn = this.nodeToTermConverter.getInSymbol(node);
        final TRSFunctionApplication nodeOut = this.nodeToTermConverter.getOutSymbol(node);

        for(Node<PrologAbstractState> succ : this.graph.getOut(node)) {
            final TRSFunctionApplication succIn = this.nodeToTermConverter.getInSymbol(succ);
            final TRSFunctionApplication succOut = this.nodeToTermConverter.getOutSymbol(succ);

            returnValue.add(this.ruleFactory.createUnconditionalRule(nodeIn, succIn));
            returnValue.add(this.ruleFactory.createUnconditionalRule(succOut, nodeOut));
        }

        return returnValue;
    }

    TRSFunctionApplication negateArithComp(TRSFunctionApplication comparison) {
        switch(comparison.getRootSymbol().getName()) {
        case "!": {
            assert comparison.getArgument(0) instanceof TRSFunctionApplication;
            assert ((TRSFunctionApplication)comparison.getArgument(0)).getRootSymbol().getName().equals("=");
            return TRSTerm.createFunctionApplication(FunctionSymbol.create("=", 2), comparison.getArgument(0), comparison.getArgument(1));
        }
        case "<=": {
            return TRSTerm.createFunctionApplication(FunctionSymbol.create(">", 2), comparison.getArgument(0), comparison.getArgument(1));
        }
        case "<": {
            return TRSTerm.createFunctionApplication(FunctionSymbol.create(">=", 2), comparison.getArgument(0), comparison.getArgument(1));
        }
        case ">=": {
            return TRSTerm.createFunctionApplication(FunctionSymbol.create("<", 2), comparison.getArgument(0), comparison.getArgument(1));
        }
        case ">": {
            return TRSTerm.createFunctionApplication(FunctionSymbol.create("<=", 2), comparison.getArgument(0), comparison.getArgument(1));
        }
        case "=": {
            return TRSTerm.createFunctionApplication(FunctionSymbol.create("!", 1), TRSTerm.createFunctionApplication(FunctionSymbol.create("=", 2), comparison.getArgument(0), comparison.getArgument(1)));
        }
        default:
            assert false : "Unknown comparison symbol";
            return null;
        }
    }
}
