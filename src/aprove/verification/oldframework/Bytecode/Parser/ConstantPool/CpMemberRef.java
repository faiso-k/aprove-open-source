package aprove.verification.oldframework.Bytecode.Parser.ConstantPool;

public interface CpMemberRef extends CPEntry {

    int getClassIndex();

    int getNameAndTypeRefIndex();

}
