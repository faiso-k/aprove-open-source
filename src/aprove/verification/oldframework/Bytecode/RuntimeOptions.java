package aprove.verification.oldframework.Bytecode;

/**
 * Runtime options that should be set before analysis starts.
 * This includes information about how static fields look like if the corresponding class is assumed to be initialized
 * already.
 * We also specify which classes are assumed to exist when the analysis starts.
 * @author cotto
 */
public class RuntimeOptions {

    /**
     * Specifying annotations for static fields for classes which are assumed to be initialized already.
     */
    private final StaticFieldInitInfo staticFieldInitInfo;

    /**
     * @param staticFieldInitInfoParam specifying annotations for static fields for classes which are assumed to be initialized already.
     * @param defaultClassInitStateParam specifying if classes are assumed to already be initialized.
     */
    public RuntimeOptions(final StaticFieldInitInfo staticFieldInitInfoParam) {
        this.staticFieldInitInfo = staticFieldInitInfoParam;
    }

    /**
     * @return annotations for static fields for classes which are assumed to be initialized already.
     */
    public StaticFieldInitInfo getStaticFieldInitInfo() {
        return this.staticFieldInitInfo;
    }

}
