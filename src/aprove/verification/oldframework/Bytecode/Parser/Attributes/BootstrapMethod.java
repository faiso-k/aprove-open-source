package aprove.verification.oldframework.Bytecode.Parser.Attributes;

import java.util.*;

public class BootstrapMethod {

    private short bootstrapMethodRef;
    private List<Short> bootstrapArguments;

    public BootstrapMethod(short bootstrapMethodRef, List<Short> bootstrapArguments) {
        this.bootstrapMethodRef = bootstrapMethodRef;
        this.bootstrapArguments = bootstrapArguments;
    }

    public short getBootstrapMethodRef() {
        return bootstrapMethodRef;
    }

    public List<Short> getBootstrapArguments() {
        return bootstrapArguments;
    }

}
