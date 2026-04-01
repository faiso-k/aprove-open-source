package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.oldframework.Utility.*;

/**
 *
 * @author MP
 */
public enum ImplicationType implements IDPExportable {

    SOUND {
        @Override
        public boolean isSound() {
            return true;
        }

        @Override
        public boolean isComplete() {
            return false;
        }

        @Override
        public ImplicationType invert() {
            return COMPLETE;
        }

        @Override
        public ImplicationType mult(final ImplicationType other) {
            switch(other) {
            case SOUND:
                return SOUND;
            case COMPLETE:
                return UNRELATED;
            case EQUIVALENT:
                return SOUND;
            case UNRELATED:
                return UNRELATED;
            default :
                throw new IllegalArgumentException("unknown combination");
            }
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append(eu.sound());
        }

        @Override
        public boolean subsumes(final ImplicationType other) {
            return !other.isComplete();
        }
    },

    COMPLETE {
        @Override
        public boolean isSound() {
            return false;
        }

        @Override
        public boolean isComplete() {
            return true;
        }

        @Override
        public ImplicationType invert() {
            return SOUND;
        }

        @Override
        public boolean subsumes(final ImplicationType other) {
            return !other.isSound();
        }

        @Override
        public ImplicationType mult(final ImplicationType other) {
            switch(other) {
            case SOUND:
                return UNRELATED;
            case COMPLETE:
                return COMPLETE;
            case EQUIVALENT:
                return COMPLETE;
            case UNRELATED:
                return UNRELATED;
            default :
                throw new IllegalArgumentException("unknown combination");
            }
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append(eu.complete());
        }
    },

    EQUIVALENT {
        @Override
        public boolean isSound() {
            return true;
        }

        @Override
        public boolean isComplete() {
            return true;
        }

        @Override
        public ImplicationType invert() {
            return EQUIVALENT;
        }

        @Override
        public boolean subsumes(final ImplicationType other) {
            return true;
        }

        @Override
        public ImplicationType mult(final ImplicationType other) {
            switch(other) {
            case SOUND:
                return SOUND;
            case COMPLETE:
                return COMPLETE;
            case EQUIVALENT:
                return EQUIVALENT;
            case UNRELATED:
                return UNRELATED;
            default :
                throw new IllegalArgumentException("unknown combination");
            }
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append(eu.equivalent());
        }
    },

    UNRELATED {

        @Override
        public boolean isSound() {
            return false;
        }

        @Override
        public boolean isComplete() {
            return false;
        }

        @Override
        public ImplicationType invert() {
            return UNRELATED;
        }

        @Override
        public ImplicationType mult(final ImplicationType other) {
            return UNRELATED;
        }

        @Override
        public boolean subsumes(final ImplicationType other) {
            return other == UNRELATED;
        }

        @Override
        public void export(final StringBuilder sb,
            final Export_Util eu,
            final VerbosityLevel verbosityLevel) {
            sb.append(eu.notSign());
            sb.append(eu.equivalent());
        }
    };

    public abstract boolean isSound();
    public abstract boolean isComplete();

    /**
     * inverts sound and complete
     * @return
     */
    public abstract ImplicationType invert();

    public abstract ImplicationType mult(ImplicationType other);

    public abstract boolean subsumes(ImplicationType other);

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }
}
