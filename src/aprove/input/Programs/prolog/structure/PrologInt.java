package aprove.input.Programs.prolog.structure;

import java.math.*;

/**
 * Represents an integer in Prolog.<br><br>
 *
 * Created: May 5, 2006<br>
 * Last modified: Dec 13, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologInt extends PrologNumber {

    /**
     * The integer value.
     */
    private final BigInteger value;

    /**
     * Constructs a new PrologInt with the specified value. The integer's
     * name is set to its value.
     * @param valueParam The integer's value.
     */
    public PrologInt(final BigInteger valueParam) {
        super(valueParam.toString());
        this.value = valueParam;
    }

    /**
     * Constructs a new PrologInt with the specified name. This name
     * must be a legal integer representation in Prolog and is parsed to
     * an int value which is internally stored.
     * @param name The integer's name.
     */
    public PrologInt(final String name) {
        super(name);
        this.value = PrologInt.parse(name);
    }

    /**
     * Helper method for parsing characters in base representations of
     * integers in Prolog.
     * @param c A character to parse to a base value.
     * @return The character's base value.
     */
    private static int charToInt(final char c) {
        switch (c) {
        case '0':
            return 0;
        case '1':
            return 1;
        case '2':
            return 2;
        case '3':
            return 3;
        case '4':
            return 4;
        case '5':
            return 5;
        case '6':
            return 6;
        case '7':
            return 7;
        case '8':
            return 8;
        case '9':
            return 9;
        default:
            return PrologInt.lowCharToInt1(Character.toLowerCase(c));
        }
    }

    /**
     * This helper supports charToInt and only works for lower case characters up to k. These methods only exist,
     * because checkstyle thinks that it is a good idea to split big switch-blocks into several parts...
     * @param c The lower case character.
     * @return The character's base value.
     */
    private static int lowCharToInt1(final char c) {
        switch (c) {
        case 'a':
            return 10;
        case 'b':
            return 11;
        case 'c':
            return 12;
        case 'd':
            return 13;
        case 'e':
            return 14;
        case 'f':
            return 15;
        case 'g':
            return 16;
        case 'h':
            return 17;
        case 'i':
            return 18;
        case 'j':
            return 19;
        case 'k':
            return 20;
        default:
            return PrologInt.lowCharToInt2(c);
        }
    }

    /**
     * This helper supports charToInt and only works for lower case characters from l. These methods only exist,
     * because checkstyle thinks that it is a good idea to split big switch-blocks into several parts...
     * @param c The lower case character.
     * @return The character's base value.
     */
    private static int lowCharToInt2(final char c) {
        switch (c) {
        case 'l':
            return 21;
        case 'm':
            return 22;
        case 'n':
            return 23;
        case 'o':
            return 24;
        case 'p':
            return 25;
        case 'q':
            return 26;
        case 'r':
            return 27;
        case 's':
            return 28;
        case 't':
            return 29;
        case 'u':
            return 30;
        case 'v':
            return 31;
        default:
            throw new NumberFormatException("Cannot convert character!");
        }
    }

    /**
     * Helper method for parsing a String with an integer representation
     * in Prolog to an int value.
     * @param param The integer representation.
     * @return The parsed int value.
     */
    private static BigInteger parse(final String param) {
        BigInteger res = null;
        boolean neg = false;
        String name = param;
        if (name.startsWith("-")) {
            neg = true;
            name = name.substring(1);
        } else if (name.startsWith("+")) {
            name = name.substring(1);
        }
        if (name.startsWith("0'")) {
            final char[] help = new char[1];
            name.getChars(2, 3, help, 0);
            res = BigInteger.valueOf(help[0]);
        } else if (name.startsWith("'", 1)) {
            res = PrologInt.parseBase(Integer.parseInt(name.substring(0, 1)), name.substring(2));
        } else if (name.startsWith("'", 2)) {
            res = PrologInt.parseBase(Integer.parseInt(name.substring(0, 2)), name.substring(3));
        } else if (name.startsWith("0b")) {
            res = PrologInt.parseBase(2, name.substring(2));
        } else if (name.startsWith("0o")) {
            res = PrologInt.parseBase(8, name.substring(2));
        } else if (name.startsWith("0x")) {
            res = PrologInt.parseBase(16, name.substring(2));
        } else {
            res = PrologInt.parseBase(10, name);
        }
        if (neg) {
            res = res.negate();
        }
        return res;
    }

    /**
     * Helper method for parsing a String with an integer representation
     * in Prolog to an int value considering a base for parsing the
     * String.
     * @param base The base by which the String is parsed to an int value.
     * @param toParse The String to parse.
     * @return The parsed int value of the specified String.
     */
    private static BigInteger parseBase(final int base, final String toParse) {
        // See the Prolog documentation for information about base limits
        if (base > 36 || base < 2) {
            throw new NumberFormatException("Illegal base!");
        }
        //TODO consider the (unlikely) case that we have a String exceeding an int array length?
        final BigInteger bigBase = BigInteger.valueOf(base);
        final char[] chars = toParse.toCharArray();
        final int length = chars.length;
        BigInteger res = BigInteger.ZERO;
        for (int i = 0; i < length; i++) {
            final int test = PrologInt.charToInt(chars[length - i - 1]);
            if (test >= base) {
                throw new NumberFormatException("Values are not within base limits!");
            }
            res = res.add(bigBase.pow(i).multiply(BigInteger.valueOf(test)));
        }
        return res;
    }

    @Override
    public boolean equals(final Object o) {
        if (o instanceof PrologInt) {
            return this.value == ((PrologInt) o).value;
        }
        return false;
    }

    /**
     * Returns the integer's value.
     * @return The integer's value.
     */
    public BigInteger getValue() {
        return this.value;
    }

    @Override
    public int hashCode() {
        return 97 * this.value.hashCode();
    }

    @Override
    public boolean isInt() {
        return true;
    }

    @Override
    public PrologTerm rename(final String oldName, final String newName, final int arity) {
        if (arity == 0 && this.getName().equals(oldName)) {
            return new PrologInt(newName);
        } else {
            return this;
        }
    }

    @Override
    public PrologTerm replaceName(final String name) {
        return new PrologInt(name);
    }

}
