package aprove.input.Utility;

import java.io.*;

/**
 * A filtering reader that passes input through unmodified,
 * unless it encounters a backslash followed by the character 'u'
 * (unless preceded by an odd number of backslashes).
 * If it encounters such a unicode escape, the next four characters
 * are taken to be a hexadecimal number denoting an unicode char,
 * and the escape is replaced by that character.
 * This implements JLS, Section 3.3 ("Unicode Escapes")
 *
 * The current implementation is pretty inefficient. If this class is used
 * heavily, spending some time on a better implementation is recommended.
 */
public class JavaUnicodeEscapeReader extends Reader {
    /*
     * Note: As this _is_ java code, be careful not to put the sequence
     * "\" + "u" anywhere, even in comments.
     * The compile would fail because that's the exact escape we're parsing,
     * and it'd probably be an invalid escape.
     */

    private final Reader source;
    private int nextChar = -1;

    public JavaUnicodeEscapeReader(Reader source) {
        super(source);
        this.source = source;
    }

    @Override
    public int read() throws IOException {
        synchronized(this.lock) {
            return this.fetchOneChar();
        }
    }

    @Override
    public int read(char[] cbuf, int off, int len) throws IOException {
        // Really cheap implementation: We shouldn't block after producing
        // at least one character, and we cannot predict whether reading
        // another character will block. So we only read one.

        // To improve this, you will have to write parseOneChar such that it
        // aggressively uses source.ready() and keeps its state inside
        // instance variables, so the call can stop in the middle of parsing
        // a Unicode escape and can later resume at that point.

        int charOrEOF = this.fetchOneChar();
        if (charOrEOF == -1) {
            return -1;
        }

        cbuf[off] = (char) charOrEOF;
        return 1;
    }

    protected int fetchOneChar() throws IOException {
        assert Thread.holdsLock(this.lock);
        if (this.nextChar != -1) {
            if (this.nextChar == -2) {
                throw new IOException("Reader closed.");
            }
            int result = this.nextChar;
            this.nextChar = -1;
            return result;
        }
        return this.parseOneChar();
    }

    protected int parseOneChar() throws IOException {
        assert Thread.holdsLock(this.lock);
        int maybeBackslash = this.source.read();
        if (maybeBackslash != '\\') {
            return maybeBackslash;
        }

        // Okay, we have a backslash. What now?
        int following = this.source.read();
        if (following != 'u') {
            // Boring. Return those two characters on the next read requests
            this.nextChar = following;
            return maybeBackslash; // really a backslash, at this point.
        }

        // Okay, we have what we wrote this class for.
        // Strip further 'u' characters
        while (following == 'u') {
            following = this.source.read();
        }

        // Collect four hex digits
        int result = 0;
        int i=0;
        while(true) {
            result = (result << 4) | this.parseHex(following);
            if (++i == 4) {
                break;
            }
            following = this.source.read();
        }
        return result;
    }

    private int parseHex(int character) throws IOException {
        if (character >= '0' && character <= '9') {
            return character - '0';
        }
        if (character >= 'A' && character <= 'F') {
            return character - 'A' + 10;
        }
        if (character >= 'a' && character <= 'f') {
            return character - 'a' + 10;
        }
        throw new CharConversionException("Invalid hex character " + character + "in unicode escape");
    }

    @Override
    public boolean ready() throws IOException {
        if (this.nextChar == -2) {// closed
            throw new IOException("Reader closed");
        }
        // As \ uuuuuuuuuuu<hex> may be arbitrarily long, we can never guarantee
        // that we won't block unless we have a character stashed away
        return (this.nextChar != -1);
    }

    @Override
    public void close() throws IOException {
        this.source.close();
        this.nextChar = -2;
    }
}
