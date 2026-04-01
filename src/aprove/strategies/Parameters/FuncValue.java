package aprove.strategies.Parameters;

import aprove.strategies.Util.*;


public class FuncValue implements ParamValue {
    private final String name;
    private final FrozenParameters params;

    public FuncValue(String name, FrozenParameters params) {
        this.name = name;
        this.params = params;
    }

    public String getName() {
        return this.name;
    }

    public FrozenParameters getParams() {
        return this.params;
    }

    @Override
    public Object get(StrategyProgram program) throws WrappedParamMgrException {
        try {
            NameDefinition declaration = program.getDeclaration(this.name);
            return program.creator.build(this.name, this.params, declaration);
        } catch (ParameterManagerException e) {
            throw new WrappedParamMgrException("While building " + this.toString(), e);
        }
    }

    @Override
    public Object getOrCoerce(StrategyProgram program, Class<?> expectedClass,
            Class<?> targetClass) throws WrappedParamMgrException {
        if (program.isDeclaredName(this.name)) {
            return this.get(program);
        }

        try {
            if (! this.params.isEmpty()) {
                // coercions only work for bare words, if we have further parameters
                // we already have an error here.
                throw new UserErrorException("No declaration found");
            }
            return ObjectCreator.coerce(targetClass, this.name, expectedClass);
        } catch (ParameterManagerException e) {
            throw new WrappedParamMgrException("While coercing " + this.name + " to " + expectedClass.getSimpleName(), e);
        }
    }

    @Override
    public String toString() {
        if (this.params.isEmpty()) {
            return this.name;
        } else {
            return this.name + this.params.toString();
        }
    }
}
