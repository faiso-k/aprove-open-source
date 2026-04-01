package aprove.strategies.InstantiationUtils;

import java.util.*;

import aprove.strategies.UserStrategies.*;
import aprove.strategies.Util.*;

public class StratAsListWrapper extends StrategyCreator {
    private final String listParamName;

    public StratAsListWrapper(ParametrizedCreator backend, String listParamName) {
        super(backend);
        this.listParamName = listParamName;
    }

    @Override
    public void acceptStrategies(List<UserStrategy> subStrategies) throws ParameterManagerException {
        this.setParameter(this.listParamName, subStrategies);
    }
}
