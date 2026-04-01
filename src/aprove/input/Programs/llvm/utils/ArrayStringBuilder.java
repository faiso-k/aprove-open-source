package aprove.input.Programs.llvm.utils;

public class ArrayStringBuilder {

    private StringBuilder bld;

    public ArrayStringBuilder() {
        this.bld = new StringBuilder();
        this.bld.append("[\n");
    }

    @Override
    public String toString(){
        this.bld.append("\n]");
        return this.bld.toString();
    }

    public void append(String val){
        this.bld.append(",\n");
        this.bld.append(val);
    }

}
