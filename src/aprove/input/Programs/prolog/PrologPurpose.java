package aprove.input.Programs.prolog;

/**
 * @author cryingshadow
 * Contains all analysis purposes for Prolog programs.
 */
public enum PrologPurpose {

    /**
     * @author cryingshadow
     * We want to analyze runtime complexity.
     */
    COMPLEXITY {
        @Override
        public String toString() {
            return "Runtime Complexity";
        }
    },

    /**
     * @author cryingshadow
     * We want to analyze determinacy.
     */
    DETERMINACY {
        @Override
        public String toString() {
            return "Determinacy";
        }
    },

    /**
     * @author cryingshadow
     * We want to analyze termination.
     */
    TERMINATION {
        @Override
        public String toString() {
            return "Left Termination";
        }
    };

    /**
     * Checks whether the purpose belongs to a runtime analysis, i.e., termination or runtime complexity analysis.
     * @param purpose The purpose to check.
     * @return True if the specified purpose is termination or runtime complexity.
     */
    public static boolean isRuntimeAnalysis(final PrologPurpose purpose) {
        switch (purpose) {
        case TERMINATION:
        case COMPLEXITY:
            return true;
        default:
            return false;
        }
    }

}
