package aprove.input.Programs.prolog.structure;

/**
 * @author cryingshadow
 * Contains all moding values which we consider for our analyses.
 */
public enum Moding {

    /**
     * Indicates that the corresponding argument can be anything.
     */
    ANY {

        /* (non-Javadoc)
         * @see java.lang.Enum#toString()
         */
        @Override
        public String toString() {
            return "a";
        }

    },

    /**
     * Indicates that the corresponding argument is a ground term.
     */
    GROUND {

        /* (non-Javadoc)
         * @see java.lang.Enum#toString()
         */
        @Override
        public String toString() {
            return "g";
        }

    },

    /**
     * Indicates that the corresponding argument is an integer.
     */
    NUMBER {

        /* (non-Javadoc)
         * @see java.lang.Enum#toString()
         */
        @Override
        public String toString() {
            return "n";
        }

    }

}
