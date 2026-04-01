package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Strips first (last) symbol on TRSs with maximum symbol arity 1 and
 * with just one rule if the first (last) symbol of the lhs is equal
 * to the first (last) symbol of the rhs of the rule.
 * 
 * Can also be used to strip whole prefixes and not just a single symbol
 *
 * @author Carsten Fuhs & Jan-Christoph Kassing
 * @version $Id$
 */
public class StripSymbolsProcessor extends QTRSProcessor {

    private final boolean wholePrefix;

    @ParamsViaArgumentObject
    public StripSymbolsProcessor(final Arguments arguments) {
        this.wholePrefix = arguments.wholePrefix;
    }
    
    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        
        final ImmutableSet<Rule> r = qtrs.getR();
        if (! (qtrs.getQ().isEmpty() && r.size() == 1
                && qtrs.getMaxArity() == 1)) {
            return false;
        }

        // we need at least two FunctionApplications
        // on each side for this to work
        final Rule theRule = r.iterator().next();

        TRSTerm arg;
        final TRSFunctionApplication lhs = theRule.getLeft();
        if (lhs.getRootSymbol().getArity() < 1) {
            return false;
        }
        arg = lhs.getArgument(0);
        if (arg.isVariable()) {
            return false;
        }

        final TRSTerm rhs = theRule.getRight();
        if (rhs.isVariable()) {
            return false;
        }
        final TRSFunctionApplication f = (TRSFunctionApplication) rhs;
        if (f.getRootSymbol().getArity() < 1) {
            return false;
        }
        arg = f.getArgument(0);
        if (arg.isVariable()) {
            return false;
        }
        return true;
    }


    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        if (Globals.useAssertions) {
            assert this.isQTRSApplicable(qtrs);
        }
        final Rule theRule = qtrs.getR().iterator().next();
        final TRSFunctionApplication lhs = theRule.getLeft();
        final TRSTerm rhs = theRule.getRight();
        TRSFunctionApplication newLhs = null;
        TRSTerm newRhs = null;
        
        boolean prefix = false;

        // 1) try to remove the first symbol
        if (lhs.getRootSymbol().equals( ((TRSFunctionApplication) rhs).getRootSymbol())) {
            prefix = true;
            newLhs = (TRSFunctionApplication) lhs.getArgument(0);
            newRhs = ((TRSFunctionApplication)rhs).getArgument(0);
        }
        // 2) try to remove the last symbol *if it is not a constant*
        else {
            final TRSVariable newVar = TRSTerm.createVariable("x");

            // not pretty, but it works
            Set<Position> lhsPositions, rhsPositions;

            // first try to strip the rhs term
            rhsPositions = rhs.getPositions();
            Position rhsDeepestPos = null;
            int maxDepth = -1;
            for (final Position p : rhsPositions) {
                // there is always at least one position
                final int pDepth = p.getDepth();
                if (pDepth > maxDepth) {
                    maxDepth = pDepth;
                    rhsDeepestPos = p;
                }
            }
            if (rhs.getSubterm(rhsDeepestPos).isVariable()) {
                // otherwise we cannot perform any stripping inside

                final Position rhsSecondDeepestPos = rhsDeepestPos.shorten(1);

                // then strip the lhs (will work if we have got this far
                // because if the rhs has a variable as leaf, then so
                // must the lhs of the term rewrite rule
                lhsPositions = lhs.getPositions();
                Position lhsDeepestPos = null;
                maxDepth = -1;
                for (final Position p : lhsPositions) {
                    // there is always at least one position
                    final int pDepth = p.getDepth();
                    if (pDepth > maxDepth) {
                        maxDepth = pDepth;
                        lhsDeepestPos = p;
                    }
                }
                if (Globals.useAssertions) {
                    assert lhs.getSubterm(lhsDeepestPos).isVariable();
                }
                final Position lhsSecondDeepestPos = lhsDeepestPos.shorten(1);
                if (lhs.getSubterm(lhsSecondDeepestPos).equals(rhs.getSubterm(rhsSecondDeepestPos))) {
                    newLhs = (TRSFunctionApplication) lhs.replaceAt(lhsSecondDeepestPos, newVar);
                    newRhs = rhs.replaceAt(rhsSecondDeepestPos, newVar);
                }
            }
        }
        if (newLhs == null) { // no success
            return ResultFactory.unsuccessful();
        }
        
        // 3) Repeat until wholePrefix is gone
        if(this.wholePrefix) {
            boolean change = true;
            while(change) {
                change = false;
                TRSFunctionApplication recursiveLhs = newLhs;
                TRSTerm recursiveRhs = newRhs;
                if(prefix) {
                    if (recursiveLhs.getRootSymbol().equals( ((TRSFunctionApplication) recursiveRhs).getRootSymbol())) {
                        newLhs = (TRSFunctionApplication) recursiveLhs.getArgument(0);
                        newRhs = ((TRSFunctionApplication)recursiveRhs).getArgument(0);
                        change = true;
                    }
                } else {
                    final TRSVariable newVar = TRSTerm.createVariable("x");

                    // not pretty, but it works
                    Set<Position> lhsPositions, rhsPositions;

                    // first try to strip the recursiveRhs term
                    rhsPositions = recursiveRhs.getPositions();
                    Position rhsDeepestPos = null;
                    int maxDepth = -1;
                    for (final Position p : rhsPositions) {
                        // there is always at least one position
                        final int pDepth = p.getDepth();
                        if (pDepth > maxDepth) {
                            maxDepth = pDepth;
                            rhsDeepestPos = p;
                        }
                    }
                    if (recursiveRhs.getSubterm(rhsDeepestPos).isVariable()) {
                        // otherwise we cannot perform any stripping inside

                        final Position rhsSecondDeepestPos = rhsDeepestPos.shorten(1);

                        // then strip the recursiveLhs (will work if we have got this far
                        // because if the recursiveRhs has a variable as leaf, then so
                        // must the recursiveLhs of the term rewrite rule
                        lhsPositions = recursiveLhs.getPositions();
                        Position lhsDeepestPos = null;
                        maxDepth = -1;
                        for (final Position p : lhsPositions) {
                            // there is always at least one position
                            final int pDepth = p.getDepth();
                            if (pDepth > maxDepth) {
                                maxDepth = pDepth;
                                lhsDeepestPos = p;
                            }
                        }
                        if (Globals.useAssertions) {
                            assert recursiveLhs.getSubterm(lhsDeepestPos).isVariable();
                        }
                        final Position lhsSecondDeepestPos = lhsDeepestPos.shorten(1);
                        if (recursiveLhs.getSubterm(lhsSecondDeepestPos).equals(recursiveRhs.getSubterm(rhsSecondDeepestPos))) {
                            newLhs = (TRSFunctionApplication) recursiveLhs.replaceAt(lhsSecondDeepestPos, newVar);
                            newRhs = recursiveRhs.replaceAt(rhsSecondDeepestPos, newVar);
                            change = true;
                        }
                    }
                }
            }
        }

        final Rule newRule = Rule.create(newLhs, newRhs);
        final Set<Rule> newRules = Collections.singleton(newRule);
        final QTRSProblem newQtrs = QTRSProblem.create(ImmutableCreator.create(newRules));
        final QTRSProof proof = new StripSymbolsProof(qtrs, newQtrs);
        return ResultFactory.proved(newQtrs, YNMImplication.SOUND, proof);
    }

    private final class StripSymbolsProof extends QTRSProof {

        private final QTRSProblem before;
        private final QTRSProblem after;

        private StripSymbolsProof(final QTRSProblem before, final QTRSProblem after) {
            this.shortName = "Strip Symbols Proof";
            this.longName = this.shortName;
            this.before = before;
            this.after = after;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder(64);
            s.append(o.export("We were given the following TRS:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.before.getR(), Export_Util.RULES));
            s.append(o.cond_linebreak());
            s.append(o.export("By stripping symbols from the only rule of the system, we obtained the following TRS " + o.cite(Citation.ENDRULLIS) + ": "));
            s.append(o.cond_linebreak());
            s.append(o.set(this.after.getR(), Export_Util.RULES));
            return s.toString();
        }

        public String toBibTeX() {
            return "";
        }

    }

    public static class Arguments {
        public boolean wholePrefix = false;
    }

}
