package aprove.verification.dpframework.Utility;

import immutables.*;

/**
 * Empty NameProvider.
 *
 * <p>This {@link NameProvider} does not contain any name</p>
 *
 * @author noschinski
 */
public class EmptyNameProvider implements NameProvider, Immutable {

    private static final EmptyNameProvider INSTANCE =
        new EmptyNameProvider();

    private EmptyNameProvider() {
    }

    public static EmptyNameProvider create() {
        return EmptyNameProvider.INSTANCE;
    }

    @Override
    public boolean contains(String name) {
        return false;
    }
}
