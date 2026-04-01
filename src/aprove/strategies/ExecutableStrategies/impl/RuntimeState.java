package aprove.strategies.ExecutableStrategies.impl;

import java.util.*;

import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import immutables.*;

class RuntimeState {
    private final DefaultMachine machineImpl;
    private final Integer id;
    final StrategyProgram program;
    private final Map<Metadata, Object> metadata;

    RuntimeState(DefaultMachine machineImpl, Integer id, StrategyProgram program, Map<Metadata, Object> metadata) {
        this.machineImpl = machineImpl;
        this.id = id;
        this.program = program;

        if (metadata == null) {
            this.metadata = Collections.emptyMap();
        } else {
            this.metadata = ImmutableCreator.create(metadata);
        }
    }

    Object getMetadata(Metadata key) {
        return this.metadata.get(key);
    }

    public void execute() {
        this.machineImpl.execute(this.id);
    }
}
