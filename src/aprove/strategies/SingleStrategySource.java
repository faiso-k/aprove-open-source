package aprove.strategies;

import aprove.input.Utility.*;
import aprove.strategies.Parameters.*;
import aprove.verification.oldframework.Input.*;

public class SingleStrategySource implements StrategySource {

    private StrategyProgram program;

    public SingleStrategySource(StrategyProgram program) {
        this.program = program;
    }

    @Override
    public StrategyProgram getStrategyProgram(AnnotatedInput annotatedInput) {
        if (this.program == null) {
            this.program = AutoManager.getStrategyProgramForTypedInput(annotatedInput.getTypedInput());
        }
        return this.program;
    }

}
