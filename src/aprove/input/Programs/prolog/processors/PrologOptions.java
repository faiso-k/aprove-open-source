package aprove.input.Programs.prolog.processors;

import aprove.verification.oldframework.IntegerReasoning.smt.*;

/**
 * This class is used for all kinds of options, processor arguments, debug
 * flags, ...
 */
public class PrologOptions {

    /**
     * Flag whether to use the ComplexityHeuristic or the Termination Heuristic.
     */
    private boolean complexityHeuristic;

    /**
     * Flag whether the graph shall be exported graphically.
     */
    private boolean exportTree;

    /**
     * Indicates whether to use the force option for TOCL09 (1) or not (0) or both in parallel (2).
     */
    private int force;

    /**
     * The maximal number of nested function symbols before generalizing terms.
     */
    private int generalizationDepth;

    /**
     * The position where to replace nested function symbols by a fresh variable (i.e., the number of remaining nested
     * function symbols plus one).
     */
    private int generalizationPosition;

    /**
     * Maximal branching factor where generalization is not necessarily tried.
     */
    private int maxBranchingFactor;

    /**
     * Minimal number of evaluations steps before generalizations are tried.
     */
    private int minExSteps;

    /**
     * Flag whether instances which lose groundness information are not allowed.
     */
    private boolean noGroundLoss;

    /**
     * Flag whether to show the graph after its construction (for debugging).
     */
    private boolean showTree;

    /**
     * The SMT setting.
     */
    private FrontendSMT smt;

    /**
     * Limit up to where the graph shall be exported graphically.
     */
    private int treeLimit;

    /**
     * Flag whether to use TRSs in addition to PiTRSs.
     */
    private boolean trs;

    /**
     * Fill the fields with sane default values.
     */
    public PrologOptions() {
        this.complexityHeuristic = false;
        this.exportTree = false;
        this.force = 2;
        this.generalizationDepth = 7;
        this.generalizationPosition = 2;
        this.maxBranchingFactor = 3;
        this.minExSteps = 2;
        this.noGroundLoss = false;
        this.showTree = false;
        this.treeLimit = 50;
        this.trs = false;
        this.smt = FrontendSMT.Z3EXT;
    }

    /**
     * @return the force
     */
    public int getForce() {
        return this.force;
    }

    /**
     * @return the generalizationDepth
     */
    public int getGeneralizationDepth() {
        return this.generalizationDepth;
    }

    /**
     * @return the generalizationPosition
     */
    public int getGeneralizationPosition() {
        return this.generalizationPosition;
    }

    /**
     * @return the maxBranchingFactor
     */
    public int getMaxBranchingFactor() {
        return this.maxBranchingFactor;
    }

    /**
     * @return the minExSteps
     */
    public int getMinExSteps() {
        return this.minExSteps;
    }

    /**
     * @return The SMT setting.
     */
    public FrontendSMT getSmt() {
        return this.smt;
    }

    /**
     * @return the treeLimit
     */
    public int getTreeLimit() {
        return this.treeLimit;
    }

    /**
     * @return the complexityHeuristic
     */
    public boolean isComplexityHeuristic() {
        return this.complexityHeuristic;
    }

    /**
     * @return the exportTree
     */
    public boolean isExportTree() {
        return this.exportTree;
    }

    /**
     * @return the noGroundLoss
     */
    public boolean isNoGroundLoss() {
        return this.noGroundLoss;
    }

    /**
     * @return the showTree
     */
    public boolean isShowTree() {
        return this.showTree;
    }

    /**
     * @return the trs
     */
    public boolean isTrs() {
        return this.trs;
    }

    /**
     * @param compHeuristic the complexityHeuristic to set
     */
    public void setComplexityHeuristic(final boolean compHeuristic) {
        this.complexityHeuristic = compHeuristic;
    }

    /**
     * @param exportTreeParam the exportTree to set
     */
    public void setExportTree(final boolean exportTreeParam) {
        this.exportTree = exportTreeParam;
    }

    /**
     * @param f the force to set
     */
    public void setForce(final int f) {
        this.force = f;
    }

    /**
     * @param genDepth the generalizationDepth to set
     */
    public void setGeneralizationDepth(final int genDepth) {
        this.generalizationDepth = genDepth;
    }

    /**
     * @param genPos the generalizationPosition to set
     */
    public void setGeneralizationPosition(final int genPos) {
        this.generalizationPosition = genPos;
    }

    /**
     * @param maxBranchFact the maxBranchingFactor to set
     */
    public void setMaxBranchingFactor(final int maxBranchFact) {
        this.maxBranchingFactor = maxBranchFact;
    }

    /**
     * @param minExecSteps the minExSteps to set
     */
    public void setMinExSteps(final int minExecSteps) {
        this.minExSteps = minExecSteps;
    }

    /**
     * @param noGroundLossParam the noGroundLoss to set
     */
    public void setNoGroundLoss(final boolean noGroundLossParam) {
        this.noGroundLoss = noGroundLossParam;
    }

    /**
     * @param showTreeParam the showTree to set
     */
    public void setShowTree(final boolean showTreeParam) {
        this.showTree = showTreeParam;
    }

    /**
     * @param smt The SMT setting.
     */
    public void setSmt(FrontendSMT smt) {
        this.smt = smt;
    }

    /**
     * @param treeLimitParam the treeLimit to set
     */
    public void setTreeLimit(final int treeLimitParam) {
        this.treeLimit = treeLimitParam;
    }

    /**
     * @param t the trs to set
     */
    public void setTrs(final boolean t) {
        this.trs = t;
    }

}
