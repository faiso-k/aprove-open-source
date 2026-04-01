package aprove.verification.oldframework.LemmaApplication;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public enum LemmaApplicationDirection {
    TOP {
        @Override
        public String toString(){return "on top";}
    },
    LEFT2RIGHT{
        @Override
        public String toString(){return "from left to right";}
    },
    RIGHT2LEFT{
        @Override
        public String toString(){return "from right to left";}
    };
}
