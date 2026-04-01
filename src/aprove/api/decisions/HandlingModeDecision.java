package aprove.api.decisions;

import java.util.*;

/**
 * This class provides information about available handling modes.
 */
public interface HandlingModeDecision {

    String getDefaultHandlingMode();

    List<String> getHandlingModes();
}
