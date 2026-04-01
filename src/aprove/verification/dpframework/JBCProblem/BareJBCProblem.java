package aprove.verification.dpframework.JBCProblem;

import static aprove.verification.oldframework.Input.HandlingMode.*;

import java.util.*;

import aprove.input.Programs.jbc.Translator;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Bytecode.JBCOptions.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;

public class BareJBCProblem extends DefaultBasicObligation {

    private Translator translator;
    private ClassStreamProvider jbcProgramStream;
    private JBCGoalConfig goalConfig = new JBCGoalConfig();

    public static StaticOption<HandlingMode> cliGoal = new StaticOption<>();
    private InstanceOption<HandlingMode> goal = new InstanceOption<>(HandlingMode.Termination, cliGoal);

    private static Collection<HandlingMode> supportedGoals = Arrays.asList(new HandlingMode[]
            {Termination, RuntimeComplexity, SpaceComplexity, SizeComplexity, MethodSummary, UserDefined});

    public BareJBCProblem(Translator translator, ClassStreamProvider jbcProgramStream, HandlingMode goal) {
        super("Bare JBC problem", "Bare JBC problem");
        assert supportedGoals.contains(goal) : goal + " not supported for JBC";
        this.translator = translator;
        this.jbcProgramStream = jbcProgramStream;
        this.goal.set(goal);
    }

    public HandlingMode getGoal() {
        return goal.get();
    }

    @Override
    public String getStrategyName() {
        return "jbc";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return goalConfig.getProofPurposeDescriptor(getGoal(), this);
    }

    @Override
    public String export(final Export_Util o) {
        return goalConfig.export(o, getGoal(), jbcProgramStream.readProgramInformation());
    }

    public Translator getTranslator() {
        return translator;
    }

    public ClassStreamProvider getJBCProgramStream() {
        return jbcProgramStream;
    }

}
