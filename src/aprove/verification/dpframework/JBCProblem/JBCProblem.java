package aprove.verification.dpframework.JBCProblem;

import aprove.input.Programs.jbc.*;
import aprove.input.Programs.jbc.Translator;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Input.*;

/**
 * A JBCProblem is the combination of some start state and the class path,
 * which describes the context of the state.
 *
 * @author cotto
 */
public class JBCProblem extends DefaultBasicObligation {
    /**
     * Some description of the input problem (usually a source code listing).
     */
    private final String problemDescription;

    /**
     * The jbc translator which can be used to create a start state.
     */
    private final Translator translator;

    /**
     * considered class path for this analysis
     */
    private final ClassPath classPath;

    private final HandlingMode goal;

    private JBCGoalConfig goalConfig = new JBCGoalConfig();

    /**
     * @param translatorParam the jbc translator which can be used to create a start state
     * @param cPath considered class path for this analysis
     * @param problemDescr some description of the input problem (usually a
     * source code listing).
     * @param complexityAnalysis whether this is a complexity (in contrast to termination) obligation.
     */
    public JBCProblem(
        final Translator translatorParam,
        final ClassPath cPath,
        final String problemDescr,
        final HandlingMode goal)
    {
        super("JBC problem", "New JBC problem");
        assert (translatorParam != null);
        assert (cPath != null);
        this.classPath = cPath;
        this.translator = translatorParam;
        this.problemDescription = problemDescr;
        this.goal = goal;
    }

    /**
     * Export our knowledge about a certain JBC program.
     * @param o export util
     * @return textual representation of the JBC program.
     */
    @Override
    public String export(final Export_Util o) {
        return goalConfig.export(o, getGoal(), problemDescription);

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return goalConfig.getProofPurposeDescriptor(getGoal(), this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return goalConfig.getStrategyName(getGoal());
    }

    /**
     * @return runtime options, e.g. how to initialize static fields when assuming the class already was initialized
     */
    public RuntimeOptions getRuntimeOptions() {
        return this.translator.getRuntimeOptions();
    }

    /**
     * @param termGraph the termination graph of the returned state
     * @return the start state for the start method (maybe with additional annotations)
     */
    public State createStartState(final TerminationGraph termGraph) {
        return this.translator.createStartState(this.classPath, termGraph);
    }

    public HandlingMode getGoal() {
        return goal;
    }

}
