package aprove.verification.oldframework.Logic;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;

/**
 * Ternary logic using YES, MAYBE and NO as values.
 * @author nowonder, thiemann
 */

public enum YNM implements TruthValue {

    /**
     * The truth value is unknown.
     */
    MAYBE {

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#and(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue and(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.and(this);
            }
            if (other == NO) {
                return NO;
            }
            return MAYBE;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#canGoTo(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public boolean canGoTo(final TruthValue newStatus) {
            return true;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#combine(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue combine(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.combine(this);
            }
            return other;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#isBool()
         */
        @Override
        public boolean isBool() {
            return false;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#isCompletelyKnown()
         */
        @Override
        public boolean isCompletelyKnown() {
            return false;
        }

        @Override
        public boolean isCompletelyUnknown() {
            return true;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.TruthValue#mult(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue mult(final TruthValue other) {
            // should behave like AND
            return this.and(other);
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#not()
         */
        @Override
        public TruthValue not() {
            return MAYBE;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#or(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue or(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.or(this);
            }
            if (other == YES) {
                return YES;
            }
            return MAYBE;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#toBool()
         */
        @Override
        public boolean toBool() {
            throw new RuntimeException("Cannot get bool value of Maybe!");
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#toColor()
         */
        @Override
        public Color toColor() {
            return Color.YELLOW;
        }

        @Override
        public boolean isOptimal() {
            return false;
        }

    },

    /**
     * The truth value is false.
     */
    NO {

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#and(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue and(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.and(this);
            }
            return NO;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#canGoTo(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public boolean canGoTo(final TruthValue newStatus) {
            return newStatus == NO;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#combine(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue combine(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.combine(this);
            }
            if (other == YES) {
                throw new RuntimeException("cannot combine NO with YES");
            }
            return NO;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#isBool()
         */
        @Override
        public boolean isBool() {
            return true;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#isCompletelyKnown()
         */
        @Override
        public boolean isCompletelyKnown() {
            return true;
        }

        @Override
        public boolean isCompletelyUnknown() {
            return false;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.TruthValue#mult(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue mult(final TruthValue other) {
            // should behave like AND
            return this.and(other);
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#not()
         */
        @Override
        public TruthValue not() {
            return YES;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#or(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue or(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.or(this);
            }
            return other;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#toBool()
         */
        @Override
        public boolean toBool() {
            return false;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#toColor()
         */
        @Override
        public Color toColor() {
            return Color.RED;
        }

        @Override
        public boolean isOptimal() {
            return true;
        }

    },

    /**
     * The truth value is true.
     */
    YES {

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#and(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue and(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.and(this);
            }
            return other;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#canGoTo(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public boolean canGoTo(final TruthValue newStatus) {
            return newStatus == YES;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#combine(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue combine(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.combine(this);
            }
            if (other == NO) {
                throw new RuntimeException("cannot combine YES with NO");
            }
            return YES;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#isBool()
         */
        @Override
        public boolean isBool() {
            return true;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#isCompletelyKnown()
         */
        @Override
        public boolean isCompletelyKnown() {
            return true;
        }

        @Override
        public boolean isCompletelyUnknown() {
            return false;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.TruthValue#mult(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue mult(final TruthValue other) {
            // should behave like AND
            return this.and(other);
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#not()
         */
        @Override
        public TruthValue not() {
            return NO;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#or(aprove.verification.oldframework.Logic.TruthValue)
         */
        @Override
        public TruthValue or(final TruthValue other) {
            if (!this.canHandle(other)) {
                return other.or(this);
            }
            return YES;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#toBool()
         */
        @Override
        public boolean toBool() {
            return true;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Logic.YNM#toColor()
         */
        @Override
        public Color toColor() {
            return Color.GREEN;
        }

        @Override
        public boolean isOptimal() {
            return true;
        }

    };

    public static TruthValue and(final Collection<TruthValue> vals) {
        TruthValue res = YES;
        for (final TruthValue val : vals) {
            res = res.and(val);
        }
        return res;
    }

    public static YNM fromBool(final boolean bool) {
        return bool ? YES : NO;
    }

    /**
     * @param truthValue Some YNM value.
     * @return The inverted YNM value.
     */
    public static YNM invert(final YNM truthValue) {
        switch (truthValue) {
        case YES:
            return YNM.NO;
        case NO:
            return YNM.YES;
        default:
            return YNM.MAYBE;
        }
    }

    public static TruthValue or(final Collection<TruthValue> vals) {
        TruthValue res = NO;
        for (final TruthValue val : vals) {
            res = res.or(val);
        }
        return res;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Logic.TruthValue#and(aprove.verification.oldframework.Logic.TruthValue)
     */
    @Override
    public abstract TruthValue and(TruthValue other);

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Logic.TruthValue#canGoTo(aprove.verification.oldframework.Logic.TruthValue)
     */
    @Override
    public abstract boolean canGoTo(TruthValue newStatus);

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Logic.TruthValue#combine(aprove.verification.oldframework.Logic.TruthValue)
     */
    @Override
    public abstract TruthValue combine(TruthValue other);

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Logic.TruthValue#fallbackToYNM()
     */
    @Override
    public YNM fallbackToYNM() {
        return this;
    }

    public abstract boolean isBool();

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Logic.TruthValue#isCompletelyKnown()
     */
    @Override
    public abstract boolean isCompletelyKnown();

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Logic.TruthValue#not()
     */
    @Override
    public abstract TruthValue not();

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Logic.TruthValue#or(aprove.verification.oldframework.Logic.TruthValue)
     */
    @Override
    public abstract TruthValue or(TruthValue other);

    public abstract boolean toBool();

    @Override
    public abstract Color toColor();

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Logic.TruthValue#toWstString()
     */
    @Override
    public String toWstString() {
        return this.toString();
    }

    protected boolean canHandle(final TruthValue other) {
        return other instanceof YNM;
    }

}
