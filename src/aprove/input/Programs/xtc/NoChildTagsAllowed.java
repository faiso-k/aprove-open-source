package aprove.input.Programs.xtc;

public class NoChildTagsAllowed extends UnsupportedOperationException {
    public NoChildTagsAllowed(String tagName) {
        super("<" + tagName + "> must not contain child tags.");
    }

}
