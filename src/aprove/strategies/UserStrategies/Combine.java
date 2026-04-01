package aprove.strategies.UserStrategies;

import java.util.*;

import aprove.*;

public abstract class Combine extends UserStrategy {

    public static class Options {
        public List<UserStrategy> subStrategies;
    }

    protected Options options;

    public Combine(Options options) {
        if (Globals.useAssertions) {
            // check for all non-null;
            List<UserStrategy> myList = new Vector<UserStrategy>();
            int n = 0;
            for (UserStrategy s : options.subStrategies) {
                if (s != null) {
                    myList.add(s);
                } else {
                    System.err.println(n+"th str. in any undefined!");
                }
                n++;
            }
            options.subStrategies = myList;
        }
        this.options = options;
    }

}
