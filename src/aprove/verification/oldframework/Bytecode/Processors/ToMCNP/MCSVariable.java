package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.math.*;

/**
 *
 * @author Matthias Hoelzel
 *
 */
public class MCSVariable {
    private final String name;

    private MCSVariable(final String name) {
        this.name = name;
    }

    private static int counter=0;

    public static MCSVariable create(final BigInteger bi) {
        return MCSVariable.create(bi, 0);
    }

    public static MCSVariable create(BigInteger bi, final Integer postfix) {
        if (bi == null) {
            return null;
        }
        String name = null;
        if (bi.compareTo(BigInteger.ZERO) < 0) {
            bi = bi.multiply(BigInteger.valueOf(-1));
            name =  "cm" + bi.toString();
        }
        else {
            name =  "c"  + bi.toString();
        }
        name += "_" + postfix;
        return new MCSVariable(name);
    }

    public static MCSVariable create() {
        MCSVariable.counter++;
        return new MCSVariable("v" + MCSVariable.counter);
    }

    public String getName() {
        return this.name;
    }

    @Override
    public boolean equals(final Object other) {
        if (other == null || !(other instanceof MCSVariable)) {
            return false;
        }
        return this.name.equals(((MCSVariable)other).name);
    }

    @Override
    public int hashCode() {
        return this.name.hashCode() + 3;
    }

    @Override
    public String toString() {
        return this.getName();
    }
}