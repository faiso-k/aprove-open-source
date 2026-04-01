package aprove.input.Programs.SMTLIB.Terms;

/**
 * Docu-guess (fuhs):
 * Generates fresh names for local and slack variables that arise when
 * parsing an SMTLIB v2 QF_NIA benchmark into a Formula&lt;Diophantine&gt;.
 *
 * Exploits the lexical requirement that an identifier name in an
 * SMTLIB v2 benchmark must not start with a digit
 * in order to generate variable names that do start with a digit and
 * hence cannot clash with variable names taken from the input file.
 *
 * This way, memory usage of instances of this class stays constant.
 * (The disadvantage here is that after 2^31 - 2 fresh names of the same
 * kind, we will have an overflow and a name that may clash with an
 * SMTLIB v2 identifier. It is however unlikely that with current
 * technology we will reach this limit for this particular application
 * in the near future.)
 */
public class FreshNameGenerator {
    public static final FreshNameGenerator FRESHNAMEGENERATOR =
        new FreshNameGenerator();

    private int currentFreshVariableNumber = 1;

    private int currITE = 1;
    private int currLET = 1;

    public String getFreshName() {
        return (this.currentFreshVariableNumber++) + "_FRESH";
    }

    public String getFreshITE() {
        return (this.currITE++) + "_ITE";
    }

    public String getFreshLET() {
        return (this.currLET++) + "_LET";
    }
}
