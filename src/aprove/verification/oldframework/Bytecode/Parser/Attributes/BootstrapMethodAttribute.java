package aprove.verification.oldframework.Bytecode.Parser.Attributes;

import java.util.*;

public class BootstrapMethodAttribute {

    private List<BootstrapMethod> bootstrapMethods;

    public BootstrapMethodAttribute(List<BootstrapMethod> bootstrapMethods) {
        this.bootstrapMethods = bootstrapMethods;
    }

    public List<BootstrapMethod> getBootstrapMethods() {
        return bootstrapMethods;
    }

}
