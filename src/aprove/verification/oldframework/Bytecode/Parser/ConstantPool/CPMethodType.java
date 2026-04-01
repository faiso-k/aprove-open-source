package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

import java.io.*;

public class CPMethodType implements CPEntry {

    private short descriptorIndex;

    public CPMethodType(short descriptorIndex) {
        this.descriptorIndex = descriptorIndex;
    }

    public short getDescriptorIndex() {
        return descriptorIndex;
    }

    @Override
    public void writeTo(DataOutputStream out) throws IOException {
        assert(false);
    }

}
