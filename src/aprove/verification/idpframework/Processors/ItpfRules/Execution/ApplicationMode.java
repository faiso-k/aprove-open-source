package aprove.verification.idpframework.Processors.ItpfRules.Execution;


/**
 *
 * @author MP
 */
public enum ApplicationMode {

    NoOp {
        @Override
        public ApplicationMode decreaseOneStep() {
            throw new UnsupportedOperationException("maybe you did an undesired operation");
        }

        @Override
        public ApplicationMode increaseOneStep() {
            return SingleStep;
        }

        @Override
        public ApplicationMode decreaseBy(final ApplicationMode usedApplications) {
            switch (usedApplications) {
            case NoOp:
                return NoOp;
            default:
                throw new IllegalArgumentException("NoOp can not be reduced");
            }
        }

        @Override
        public ApplicationMode increaseBy(final ApplicationMode usedApplications) {
            return usedApplications;
        }
    },
    SingleStep {
        @Override
        public ApplicationMode decreaseOneStep() {
            return NoOp;
        }

        @Override
        public ApplicationMode increaseOneStep() {
            return Multistep;
        }

        @Override
        public ApplicationMode decreaseBy(final ApplicationMode usedApplications) {
            switch (usedApplications) {
            case NoOp:
                return SingleStep;
            case SingleStep:
                return NoOp;
            case Multistep:
                return NoOp;
            default:
                throw new IllegalArgumentException("unknown relation");
            }
        }

        @Override
        public ApplicationMode increaseBy(final ApplicationMode usedApplications) {
            switch (usedApplications) {
            case NoOp:
                return SingleStep;
            case SingleStep:
                return Multistep;
            case Multistep:
                return Multistep;
            default:
                throw new IllegalArgumentException("unknown relation");
            }
        }

    },
    Multistep {
        @Override
        public ApplicationMode decreaseOneStep() {
            return Multistep;
        }

        @Override
        public ApplicationMode increaseOneStep() {
            return Multistep;
        }

        @Override
        public ApplicationMode decreaseBy(final ApplicationMode usedApplications) {
            return Multistep;
        }

        @Override
        public ApplicationMode increaseBy(final ApplicationMode usedApplications) {
            return Multistep;
        }

    };

    public static ApplicationMode getMode(final int stepCount) {
        if (stepCount == 0) {
            return ApplicationMode.NoOp;
        } else if (stepCount == 1) {
            return ApplicationMode.SingleStep;
        } else {
            return ApplicationMode.Multistep;
        }
    }


    public abstract ApplicationMode decreaseOneStep();
    public abstract ApplicationMode increaseOneStep();

    public abstract ApplicationMode decreaseBy(ApplicationMode usedApplications);

    public abstract ApplicationMode increaseBy(ApplicationMode usedApplications);


    public boolean isNoOp() {
        return this == NoOp;
    }

}
