package aprove.input.Programs.Strategy;

public class PrettyPrintState2 {
    private StringBuffer buffer = new StringBuffer();
    private boolean needsSpace = false;

    /**
     * A Word. Anything that should be seperated from other words with a space.
     * Line breaks are generally possible just before the start of a word.
     */
    public void appendWord(String word) {
        if (this.needsSpace) {
            this.buffer.append(" ");
        }
        this.buffer.append(word);
        this.needsSpace = true;
    }

    /**
     * We've finished a record and should start a new one. Prints a newline.
     */
    public void recordSeperator() {
        this.buffer.append('\n');
        this.needsSpace = false;
    }

    /**
     * Starts a new group, like the contents of []. Increases indent.
     */
    public void startGroup(String open) {
        this.buffer.append(open);
        this.needsSpace = false;
    }

    /**
     * Ends a group, should be matched to call of startGroup().
     */
    public void endGroup(String close) {
        this.buffer.append(close);
        this.needsSpace = true;
    }

    /**
     * A seperator, like ',', that is used to seperate entries in groups.
     * Has no space before, but space after if neccessary.
     */
    public void appendSeperator(String sep) {
        this.buffer.append(sep);
        this.needsSpace = true;
    }

    /**
     * An operator, like '=', that stands between stuff.
     * Acts pretty much like a regular word, but might be treated differently
     * when it comes to line breaks.
     */
    public void appendOperator(String op) {
        if (this.needsSpace) {
            this.buffer.append(" ");
        }
        this.buffer.append(op);
        this.needsSpace = true;
    }

    public String getContents() {
        return this.buffer.toString();
    }

}
