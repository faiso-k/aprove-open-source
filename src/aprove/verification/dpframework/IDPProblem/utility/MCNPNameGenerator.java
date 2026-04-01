package aprove.verification.dpframework.IDPProblem.utility;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Generates names by appending a fresh number to a fixed prefix.
 * Avoids elements of a set of forbidden names.
 * Provides convenience methods to get these names also as (term) Variables
 * and as (polynomial) variables.
 *
 * @author Carsten Fuhs
 */
public class MCNPNameGenerator {

    private BigInteger counter;

    private final String prefix;
    private final Set<String> forbidden;

    private MCNPNameGenerator(String prefix, Set<String> forbidden, BigInteger startIndex) {
        this.prefix = prefix;
        this.forbidden = forbidden;
        this.counter = startIndex;
    }

    private MCNPNameGenerator(String prefix, Set<String> forbidden) {
        this(prefix, forbidden, BigInteger.ZERO);
    }

    public static MCNPNameGenerator create(String prefix, Set<String> forbidden,
            BigInteger startIndex) {
        return new MCNPNameGenerator(prefix, forbidden, startIndex);
    }

    public static MCNPNameGenerator create(String prefix, Set<String> forbidden) {
        return new MCNPNameGenerator(prefix, forbidden);
    }

    public static MCNPNameGenerator createForForbiddenNames(String prefix,
            Set<? extends HasName> forbiddenNames) {
        Set<String> forbidden = aprove.verification.dpframework.BasicStructures.CollectionUtils.getNames(forbiddenNames);
        return MCNPNameGenerator.create(prefix, forbidden);
    }

    /**
     * @return a fresh new name
     */
    public String getNextName() {
        String name;
        do {
            this.counter = this.counter.add(BigInteger.ONE);
            name = this.prefix + this.counter;
        } while (this.forbidden.contains(name));
        return name;
    }

    /**
     * Convenience method.
     *
     * @return a fresh new name, conveniently wrapped into a term Variable.
     */
    public TRSVariable getNextTermVariable() {
        String nextName = this.getNextName();
        TRSVariable res = TRSTerm.createVariable(nextName);
        return res;
    }

    /**
     * Convenience method.
     *
     * @return a fresh new name, conveniently wrapped into a variable of type
     *  OrderPoly<BigIntImmutable>.
     */
    public OrderPoly<BigIntImmutable> getNextPolyVariable(IDPGInterpretation i,
            Abortion aborter) throws AbortionException {
        TRSVariable nextTermVariable = this.getNextTermVariable();
        OrderPoly<BigIntImmutable> res = i.interpretTerm(nextTermVariable, aborter);
        return res;
    }
}
