package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Refactored out of many, many Dimacs- (or Iscas-) based SATCheckers.
 *
 * @author fuhs
 */
public abstract class AbstractSATChecker implements SATChecker {

    protected static final Logger log = Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.SATCheckers.AbstractSATChecker");

    @Override
    public abstract int[] solve(String dimacs, final Abortion aborter) throws AbortionException, SolverException;

    public AbstractSATChecker() {
        super();
    }

    @Override
    public int[] solve(Formula<None> formula, final Abortion aborter) throws AbortionException, SolverException {
        String dimacsOrIscas;
        dimacsOrIscas = FormulaToDimacsConverter.convert(formula, aborter);
        if (AbstractSATChecker.log.isLoggable(Level.FINEST)) {
            AbstractSATChecker.log.log(Level.FINE, "CNF length in characters: {0}\n", dimacsOrIscas.length());
            int nlPos = dimacsOrIscas.indexOf("\n");
            AbstractSATChecker.log.fine("First line of DIMACS problem (# vars, # clauses):\n"
                    + dimacsOrIscas.substring(0, nlPos + 1));
        }
        return this.solve(dimacsOrIscas, aborter);
    }

}