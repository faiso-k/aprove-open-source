package aprove.input.Programs.Strategy;

import java.io.*;

public class PrettyPrintState {

    private int indention;
    private int posInLine;
    private int maxWidth;
    private int precedence;
    private int line;

    public PrettyPrintState() {
        this.indention = 0;
        this.posInLine = 0;
        this.maxWidth = 80;
        this.precedence = 0;
        this.line = 0;
    }

    public void indentBy(int i) {
        this.setIndention(this.getIndention() + i);
    }

    // FIXME move the following stuff to some utility class?
    public void indent(Appendable ap) throws IOException {
        int spaces = Math.max(0, this.getIndention() - this.getPosInLine());
        char[] indent = new char[spaces];
        for (int i = 0; i < indent.length; ++i) {
            indent[i] = ' ';
        }
        ap.append(new String(indent));
        this.setPosInLine(this.getPosInLine() + spaces);
    }

    public void append(Appendable ap, String s) throws IOException {
        //        assert (posInLine < 5 * maxWidth);
        ap.append(s);
        this.setPosInLine(this.getPosInLine() + s.length());
    }

    public void indentMore() {
        this.indention += 4;
    }

    public void setIndention(int indention) {
        this.indention = indention;
    }

    public int getIndention() {
        return this.indention;
    }

    public void setPosInLine(int posInLine) {
        this.posInLine = posInLine;
    }

    public int getPosInLine() {
        return this.posInLine;
    }

    public void setMaxWidth(int maxWidth) {
        this.maxWidth = maxWidth;
    }

    public int getMaxWidth() {
        return this.maxWidth;
    }

    public void setPrecedence(int precedence) {
        this.precedence = precedence;
    }

    public int getPrecedence() {
        return this.precedence;
    }

    public void setLine(int line) {
        this.line = line;
    }

    public int getLine() {
        return this.line;
    }

    public void newLine(Appendable ap) throws IOException {
        ap.append('\n');
        this.posInLine = 0;
        ++this.line;
    }
}
