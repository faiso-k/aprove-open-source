package aprove.strategies.InstantiationUtils;

import java.lang.reflect.*;
import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.strategies.UserStrategies.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.*;

public class CreatorBuilder {
    /** List of interfaces/superclasses that must be annotated to be creatable */
    private static final List<Class<?>> BLACKLIST;

    static {
        BLACKLIST = new ArrayList<Class<?>>();
        CreatorBuilder.BLACKLIST.add(UserStrategy.class);
    }

    public static StrategyCreator stratCreatorFor(Class<?> targetClass) throws ParameterManagerException {
        ParametrizedCreator backend = CreatorBuilder.buildCreatorFor(targetClass);
        AcceptsStrategiesAsList asList = targetClass.getAnnotation(AcceptsStrategiesAsList.class);
        if (asList != null) {
            return new StratAsListWrapper(backend, asList.value());
        }
        AcceptsStrategies asSeperate = targetClass.getAnnotation(AcceptsStrategies.class);
        if (asSeperate != null) {
            return new StratAsSeperateWrapper(backend, asSeperate.value(), asSeperate.optional());
        }
        return new StratUnacceptableWrapper(backend);
    }

    public static ParametrizedCreator buildCreatorFor(Class<?> targetClass) throws ParameterManagerException {
        if (targetClass.isAnnotationPresent(NoParams.class)) {
            Constructor<?> emptyConstructor;
            try {
                emptyConstructor = targetClass.getConstructor();
            } catch (NoSuchMethodException e) {
                throw new UserErrorException("Class " + targetClass.getName() +
                        " is annotated with @NoParams but has no default constructor");
            }
            return new CreatorViaArguments(emptyConstructor, new String[]{});
        }

        ParametrizedCreator result = null;
        int matches = 0;
        for(Constructor<?> constructor: targetClass.getConstructors()) {
            ParamsViaArguments argumentAnnotation = constructor.getAnnotation(ParamsViaArguments.class);
            if (argumentAnnotation != null) {
                result = new CreatorViaArguments(constructor, argumentAnnotation.value());
                matches++;
            }
            ParamsViaArgumentObject setterAnnotation = constructor.getAnnotation(ParamsViaArgumentObject.class);
            if (setterAnnotation != null) {
                Class<?>[] parameterTypes = constructor.getParameterTypes();
                if (parameterTypes.length != 1) {
                    throw new UserErrorException("Class " + targetClass.getName() +
                            " has ParamsViaArgumentObject annotation on constructor" +
                            " without exactly one argument!");
                }
                Class<?> argObjectType = setterAnnotation.value();
                if (argObjectType == void.class) {
                    argObjectType = parameterTypes[0];
                }
                result = new CreatorViaArgumentObject(constructor, argObjectType);
                matches++;
            }
            if (constructor.isAnnotationPresent(ParamsViaSetterMethods.class)) {
                if (constructor.getParameterTypes().length != 0) {
                    throw new UserErrorException("Class " + targetClass.getName() +
                            " has ParamsViaSetterMethods annotation on constructor with arguments!");
                }
                result = new LegacyCreator(targetClass);
                matches++;
            }
        }
        if (matches == 0) {
            if (Map.class.isAssignableFrom(targetClass)) {
                result = new MapCreator(targetClass);
            } else if (targetClass.isAssignableFrom(Processor.class)) {
                Constructor<?> emptyConstructor;
                try {
                    emptyConstructor = targetClass.getConstructor();
                } catch (NoSuchMethodException e) {
                    throw new UserErrorException("Class " + targetClass.getName() +
                    " has no @ParamsVia* annotation nor an default constructor");
                }
                result = new CreatorViaArguments(emptyConstructor, new String[]{});
            } else {
                for(Class<?> clazz: CreatorBuilder.BLACKLIST) {
                    if (clazz.isAssignableFrom(targetClass)) {
                        throw new UserErrorException("Unable to instantiate " + targetClass.getName() +
                        " because it is missing annotations!");
                    }
                }
                result = new LegacyCreator(targetClass);
            }
        } else if (matches > 1) {
            throw new UserErrorException("Class " + targetClass.getName() +
                    " has more than one ParamsVia* annotation!");
        }
        return result;
    }

}
