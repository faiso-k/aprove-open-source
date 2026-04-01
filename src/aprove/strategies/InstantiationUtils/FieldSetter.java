package aprove.strategies.InstantiationUtils;

import java.lang.reflect.*;

import aprove.strategies.Util.*;

class FieldSetter implements Setter {
    private Field field;

    public FieldSetter(Field field) {
        this.field = field;
    }

    @Override
    public Class<?> getExpectedType() {
        return this.field.getType();
    }

    @Override
    public void set(Object target, Object value) throws ParameterManagerException {
        try {
            this.field.set(target, value);
        } catch (IllegalArgumentException e) {
            throw new UserErrorException("Field " + this.field.getName() + " is of type " +
                    this.field.getType().getSimpleName() + " but argument is a " + value.getClass().getSimpleName());
        } catch (IllegalAccessException e) {
            throw new UnexpectedParamMgrException(e);
        }
    }

    @Override
    public String toString() {
        return "field " + this.field.toGenericString();
    }
}
