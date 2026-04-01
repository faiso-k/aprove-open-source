package aprove.input.Programs.xtc;

public class IllegalSubTagException extends IllegalArgumentException {
    public IllegalSubTagException(String parentTag, String subTag) {
        super("<" + parentTag + "> cannot contain <" + subTag + ">");
    }
}
