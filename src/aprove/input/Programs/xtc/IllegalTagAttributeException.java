package aprove.input.Programs.xtc;

public class IllegalTagAttributeException extends IllegalArgumentException {

    public IllegalTagAttributeException(XTCTagNames tag, String attribute) {
        super("<" + tag + "> cannot contain attribute " + attribute);
    }

}
