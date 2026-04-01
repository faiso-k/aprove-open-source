package aprove.xml;

public class CPFModusFactory {

    public static final CPFModus PROVE = new CPFModus() {

        @Override
        public boolean isPositive() {
            return true;
        }

        @Override
        public int negativeReason() {
            return -1;
        }

        @Override
        public String toString() {
            return "SOUNDNESS";
        }

    };

    public static final CPFModus disprove(final int position) {
        return new CPFModus() {

            @Override
            public boolean isPositive() {
                return false;
            }

            @Override
            public int negativeReason() {
                return position;
            }

            @Override
            public String toString() {
                return "COMPLETENESS w.r.t. child " + (position + 1);
            }

        };
    }

}
