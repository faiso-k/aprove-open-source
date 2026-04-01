package aprove.input.Programs.prolog.structure;

/**
 * Represents a float in Prolog.<br><br>
 *
 * Created: May 5, 2006<br>
 * Last modified: Dec 13, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class PrologFloat extends PrologNumber {

    /**
     * The float value.
     */
    private final double value;

    /**
     * Constructs a new PrologFloat with the specified value. The float's
     * name is set to its value.
     * @param valueParam The float's value.
     */
    public PrologFloat(final double valueParam) {
        super("" + valueParam);
        this.value = valueParam;
    }

    /**
     * Constructs a new PrologFloat with the specified name. This name
     * must be a legal float representation in Prolog and is parsed to
     * a double value which is internally stored.
     * @param name The float's name.
     */
    public PrologFloat(final String name) {
        super(name);
        this.value = PrologFloat.parse(name);
    }

    /**
     * Helper method for parsing a String with a float representation
     * in Prolog to a double value.
     * @param param The float representation.
     * @return The parsed double value.
     */
    private static double parse(final String param) {
        double res = 0;
        boolean neg = false;
        String name = param.toLowerCase();
        int shift = 0;
        if (name.startsWith("-")) {
            neg = true;
            name = name.substring(1);
        } else if (name.startsWith("+")) {
            name = name.substring(1);
        }
        if (name.indexOf('e') > -1) {
            final String[] parts = name.split("e");
            if (parts.length != 2) {
                throw new NumberFormatException("There must not be more than one exponent!");
            }
            name = parts[0];
            shift = Integer.parseInt(parts[1]);
        }
        res = Double.parseDouble(name);
        res = res * (10 ^ shift);
        if (neg) {
            res = -res;
        }
        return res;
    }

    @Override
    public boolean equals(final Object o) {
        if (o instanceof PrologFloat) {
            return this.value == ((PrologFloat) o).value;
        }
        return false;
    }

    /**
     * Returns the float's value.
     * @return The float's value.
     */
    public double getValue() {
        return this.value;
    }

    @Override
    public int hashCode() {
        return (int) (101 * this.value);
    }

    @Override
    public PrologTerm rename(final String oldName, final String newName, final int arity) {
        if (arity == 0 && this.getName().equals(oldName)) {
            return new PrologFloat(newName);
        } else {
            return this;
        }
    }

    @Override
    public PrologTerm replaceName(final String name) {
        return new PrologFloat(name);
    }

}
