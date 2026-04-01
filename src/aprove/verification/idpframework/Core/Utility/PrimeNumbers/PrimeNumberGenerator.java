package aprove.verification.idpframework.Core.Utility.PrimeNumbers;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.SemiRings.*;

/**
 * Just a simple sieve..
 * @author MP
 */
public class PrimeNumberGenerator {

    protected static final BigInt TWO = BigInt.TWO;

    private static final Map<BigInt, BigInt> primeFactors = new LinkedHashMap<BigInt, BigInt>();
    private static final TreeSet<BigInt> numbers = new TreeSet<BigInt>();
    {
        PrimeNumberGenerator.numbers.add(PrimeNumberGenerator.TWO);
    }
    private static BigInt lastNumber = PrimeNumberGenerator.TWO;

    private static final List<BigInt> primes = new ArrayList<BigInt>();

    private static synchronized BigInt generate(final Abortion aborter) throws AbortionException {
        do {
            for (final Map.Entry<BigInt, BigInt> primeFactor : PrimeNumberGenerator.primeFactors.entrySet()) {
                final BigInt prime = primeFactor.getKey();
                BigInt num = primeFactor.getValue();;
                do {
                    PrimeNumberGenerator.addNumbers(num);
                    PrimeNumberGenerator.numbers.remove(num);
                    num = num.add(prime);
                } while (PrimeNumberGenerator.numbers.isEmpty() || num.semiCompareTo(PrimeNumberGenerator.numbers.first()) <= 0);
                primeFactor.setValue(num);
                aborter.checkAbortion();
            }
        } while (PrimeNumberGenerator.numbers.isEmpty());

        final BigInt prime = PrimeNumberGenerator.numbers.pollFirst();
        PrimeNumberGenerator.primeFactors.put(prime, prime.add(prime));
        PrimeNumberGenerator.primes.add(prime);
        return prime;
    }

    private static void addNumbers(final BigInt num) {
        while (PrimeNumberGenerator.lastNumber.semiCompareTo(num) < 0) {
            PrimeNumberGenerator.lastNumber = PrimeNumberGenerator.lastNumber.add(BigInt.ONE);
            PrimeNumberGenerator.numbers.add(PrimeNumberGenerator.lastNumber);
        }
    }

    private int nextPrimeId;

    public PrimeNumberGenerator() {
        this.nextPrimeId = 0;
    }

    public BigInt next(final Abortion aborter) throws AbortionException {
        synchronized(PrimeNumberGenerator.primes) {
            while (this.nextPrimeId >= PrimeNumberGenerator.primes.size()) {
                PrimeNumberGenerator.generate(aborter);
            }
            return PrimeNumberGenerator.primes.get(this.nextPrimeId++);
        }
    }

}
