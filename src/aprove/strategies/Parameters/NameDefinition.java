package aprove.strategies.Parameters;

import aprove.strategies.Util.*;

public class NameDefinition implements EagerlyCheckable {
    private final String className;
    private final FrozenParameters defaults;

    private Class<?> clazz = null;

    public NameDefinition(String className, FrozenParameters defaults) {
        this.className = className;
        this.defaults = defaults;
    }

    public FrozenParameters getDefaults() {
        return this.defaults;
    }

    public Class<?> getDefinedClass() throws UnexpectedParamMgrException {
        this.init();
        return this.clazz;
    }

    @Override
    public synchronized void check(StrategyProgram program) {
        try {
            this.clazz = Class.forName(this.className);
        } catch (ClassNotFoundException e) {
            program.reportProblem("defines reference to class '" + this.className + "' which I cannot find.");
        }
        // TODO: check sanity of defaults: create Creator and try to set stuff...
    }

    private synchronized void init() throws UnexpectedParamMgrException {
        if (this.clazz != null) {
            return;
        }
        try {
            this.clazz = Class.forName(this.className);
        } catch (ClassNotFoundException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }
}
