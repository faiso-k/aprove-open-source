package aprove.verification.idpframework.Core.Utility.PrimeNumbers;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.SemiRings.*;

/**
 * Trivial divide & test algorithm
 * @author MP
 */
public class PrimeFactorization {

    public static Map<BigInt, Integer> getPrimeFactorization(final BigInt value, final Abortion aborter) throws AbortionException {
        if (value.equals(BigInt.ZERO)) {
            return Collections.emptyMap();
        } else if (value.equals(BigInt.ONE)) {
            return Collections.singletonMap(BigInt.ONE, 1);
        }

        final Map<BigInt, Integer> primeExponent = new LinkedHashMap<BigInt, Integer>();
        final PrimeNumberGenerator primes = new PrimeNumberGenerator();
        BigInteger val = value.getBigInt();
        while (!val.equals(BigInteger.ONE)) {
            final BigInt prime = primes.next(aborter);
            aborter.checkAbortion();
            int count = 0;
            do {
                final BigInteger[] divAndRemainder = val.divideAndRemainder(prime.getBigInt());
                if (divAndRemainder[1].signum() == 0) {
                    val = divAndRemainder[0];
                    count++;
                } else {
                    break;
                }
                aborter.checkAbortion();
            } while (true);

            if (count > 0) {
                primeExponent.put(prime, count);
            }
        }

        return primeExponent;
    }

}
