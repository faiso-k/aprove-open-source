package aprove.api.decisions.impl;

import java.util.*;
import java.util.function.*;
import java.util.stream.*;

public enum HandlingMode {
                          TERMINATION("Termination"),
                          RUNTIME_COMPLEXITY("Runtime Complexity"),
                          DETERMINACY("Determinacy"),
                          MEMORY_SAFETY("Memory Safety");

    private static final Map<String, HandlingMode> BY_NAME = Arrays.stream(HandlingMode.values())
                                                                   .collect(Collectors.toMap(HandlingMode::getName,
                                                                                             Function.identity()));

    public static Optional<HandlingMode> getByName(String name) {
        return Optional.ofNullable(BY_NAME.get(name));
    }

    private final String name;

    private HandlingMode(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }
}
