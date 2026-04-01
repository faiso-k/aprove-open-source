package aprove.input.Programs.xtc;

public class IllegalTagAttributeValueException extends IllegalArgumentException {

    public IllegalTagAttributeValueException(final XTCTagNames tag, final String qName, final String value) {
        super("The attribute " + qName + " of tag <" + tag + "> cannot contain value " + value);
    }

}
