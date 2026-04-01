package aprove.strategies.InstantiationUtils;

import java.util.*;

import aprove.strategies.UserStrategies.*;
import aprove.strategies.Util.*;

public class StratAsSeperateWrapper extends StrategyCreator {
    private final String[] parameterNames;
    private final boolean optional;

    public StratAsSeperateWrapper(ParametrizedCreator backend, String[] parameterNames, boolean optional) {
        super(backend);
        this.parameterNames = parameterNames;
        this.optional = optional;
    }

    @Override
    public void acceptStrategies(List<UserStrategy> subStrategies)
            throws ParameterManagerException {
        int have = subStrategies == null ? 0 : subStrategies.size();

        this.checkParameterCount(have);

        for(int i=0; i < have; i++) {
            this.setParameter(this.parameterNames[i], subStrategies.get(i));
        }
    }

    private void checkParameterCount(int have) throws UserErrorException {
        int want = this.parameterNames.length;
        if (have > want || (!this.optional && have < want)) {
            throw new UserErrorException("Expecting " + want + " strategy parameters," +
                    " but got " + have);
        }
    }
}
