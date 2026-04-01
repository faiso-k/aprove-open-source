package aprove.verification.idpframework.Algorithms.Confluence;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class CriticalPairIterator implements
        AbortableIterator<ImmutableTriple<ITerm<?>, ITerm<?>, Boolean>> {

    private static final int MASK = 0x20;

    private final IRule[] rootRules;
    private int posRoot;
    private int posOther;
    private final int n;
    private final int n_minus_1;
    private boolean nextValid;
    private ImmutableTriple<ITerm<?>, ITerm<?>, Boolean> nextCritPair;
    private Iterator<Pair<IPosition, IFunctionApplication<?>>> currentOtherPositions;
    private int count = 0;

    /**
     * a critPairIterator takes a set of rules and iterates over all critical
     * pairs. Non-root overlaps will be returned before root overlaps.
     * @param rules
     */
    CriticalPairIterator(final Set<? extends IRule> rules) {
        this.n = rules.size();
        this.n_minus_1 = this.n - 1;
        this.rootRules = new IRule[this.n];
        int i = 0;

        for (final IRule rule : rules) {
            this.rootRules[i] =
                rule.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);
            i++;
        }

        if (this.n == 0) {
            this.nextValid = true;
        } else {
            this.nextValid = false;
            this.currentOtherPositions =
                this.rootRules[0].getLeft().getNonRootNonVariablePositionsWithSubTerms().iterator();
        }
        this.posRoot = 0;
        this.posOther = 0;
        this.nextCritPair = null;
    }

    private void computeNext(final Abortion aborter) throws AbortionException {
        if (this.currentOtherPositions != null) {
            while (this.posRoot != this.n) {
                final IRule rootRule = this.rootRules[this.posRoot];
                final ITerm<?> left = rootRule.getLhsInStandardRepresentation();
                final ITerm<?> right = rootRule.getRhsInStandardRepresentation();
                while (this.posOther != this.n) {
                    final IRule otherRule = this.rootRules[this.posOther];
                    final ITerm<?> otherLeft = otherRule.getLeft();
                    final ITerm<?> otherRight = otherRule.getRight();
                    if (this.currentOtherPositions == null) {
                        this.currentOtherPositions =
                            otherLeft.getNonRootNonVariablePositionsWithSubTerms().iterator();
                    }
                    while (this.currentOtherPositions.hasNext()) {
                        this.count++;
                        if ((this.count & CriticalPairIterator.MASK) != 0) {
                            this.count = 0;
                            aborter.checkAbortion();
                        }
                        final Pair<IPosition, IFunctionApplication<?>> posAndSubLeft =
                            this.currentOtherPositions.next();
                        final IFunctionApplication<?> subLeft = posAndSubLeft.y;
                        final ISubstitution sigma = left.getMGU(subLeft);
                        if (sigma != null) {
                            final ITerm<?> otherRightSigma =
                                otherRight.applySubstitution(sigma);
                            final ITerm<?> otherLeftRightAtP_sigma =
                                otherLeft.replaceAt(posAndSubLeft.x, right).applySubstitution(
                                    sigma);
                            this.nextCritPair =
                                new ImmutableTriple<ITerm<?>, ITerm<?>, Boolean>(
                                    otherRightSigma, otherLeftRightAtP_sigma,
                                    false);
                            this.nextValid = true;
                            return;
                        }
                    }
                    this.posOther++;
                    this.currentOtherPositions = null;
                }
                this.posRoot++;
                this.posOther = 0;
            }
            this.posRoot = 0;
            this.posOther = 1;
        }

        while (this.posRoot != this.n_minus_1) {
            final IRule rootRule = this.rootRules[this.posRoot];
            final ITerm<?> left = rootRule.getLhsInStandardRepresentation();
            final ITerm<?> right = rootRule.getRhsInStandardRepresentation();
            while (this.posOther != this.n) {
                final IRule otherRule = this.rootRules[this.posOther];
                final ITerm<?> otherLeft = otherRule.getLeft();
                this.posOther++;
                final ISubstitution sigma = left.getMGU(otherLeft);
                if (sigma != null) {
                    final ITerm<?> rightSigma = right.applySubstitution(sigma);
                    final ITerm<?> otherRightSigma =
                        otherRule.getRight().applySubstitution(sigma);
                    this.nextCritPair =
                        new ImmutableTriple<ITerm<?>, ITerm<?>, Boolean>(rightSigma,
                            otherRightSigma, true);
                    this.nextValid = true;
                    return;
                }
            }
            this.posRoot++;
            this.posOther = this.posRoot + 1;
        }

        this.nextCritPair = null;
        this.nextValid = true;
    }

    @Override
    public boolean hasNext(final Abortion aborter) throws AbortionException {
        if (!this.nextValid) {
            this.computeNext(aborter);
        }
        return this.nextCritPair != null;
    }

    @Override
    public ImmutableTriple<ITerm<?>, ITerm<?>, Boolean> next(final Abortion aborter)
            throws AbortionException {
        if (this.hasNext(aborter)) {
            this.nextValid = false;
            return this.nextCritPair;
        } else {
            throw new NoSuchElementException();
        }
    }

}
