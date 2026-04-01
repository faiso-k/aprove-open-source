package aprove.api.decisions;

import java.util.*;

/**
 * This class provides information about valid evaluation strategies. 
 */
public interface EvaluationStrategyDecision {

    String getDefaultEvaluationStrategy();

    List<String> getEvaluationStrategies();
}
