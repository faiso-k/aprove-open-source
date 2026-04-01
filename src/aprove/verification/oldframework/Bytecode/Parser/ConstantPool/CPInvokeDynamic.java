package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

public class CPInvokeDynamic implements CPEntry {

    private short bootstrapMethodAttrIndex;
    private short nameAndTypeIndex;

    public CPInvokeDynamic(short bootstrapMethodAttrIndex, short nameAndTypeIndex) {
        this.bootstrapMethodAttrIndex = bootstrapMethodAttrIndex;
        this.nameAndTypeIndex = nameAndTypeIndex;
    }

    public short getBootstrapMethodAttrIndex() {
        return bootstrapMethodAttrIndex;
    }

    public short getNameAndTypeIndex() {
        return nameAndTypeIndex;
    }

    @Override
    public void writeTo(DataOutputStream out) throws IOException {
        assert(false);
    }

}
