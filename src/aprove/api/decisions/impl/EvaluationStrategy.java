package aprove.api.decisions.impl;

import java.util.*;
import java.util.function.*;
import java.util.stream.*;

public enum EvaluationStrategy {
                                INNERMOST("Innermost"),
                                FULL("Full");

    private static final Map<String, EvaluationStrategy> BY_NAME = Arrays.stream(EvaluationStrategy.values())
                                                                         .collect(Collectors.toMap(EvaluationStrategy::getName,
                                                                                                   Function.identity()));

    public static Optional<EvaluationStrategy> getByName(String name) {
        return Optional.ofNullable(BY_NAME.get(name));
    }

    private final String name;

    private EvaluationStrategy(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }
}
