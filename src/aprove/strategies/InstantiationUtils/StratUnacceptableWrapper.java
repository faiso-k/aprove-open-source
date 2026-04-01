package aprove.strategies.InstantiationUtils;

import java.util.*;

import aprove.strategies.UserStrategies.*;
import aprove.strategies.Util.*;

public class StratUnacceptableWrapper extends StrategyCreator {

    public StratUnacceptableWrapper(ParametrizedCreator backend) {
        super(backend);
    }

    @Override
    public void acceptStrategies(List<UserStrategy> subStrategies)
            throws ParameterManagerException {
        if (subStrategies != null && subStrategies.size() > 0) {
            throw new UserErrorException("Unexpected strategy parameters");
        }
    }

}
